module

public import Oberwolfach.FiniteTransitionErrors

@[expose] public section

/-! Products of transitions with their exact time indices. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def identityTransition {X : Type*} (x y : X) : ℝ := if x=y then 1 else 0

theorem identityTransition_isTransition {X : Type*} [Fintype X] :
    IsTransition (identityTransition : X → X → ℝ) := by
  constructor
  · intro x y; unfold identityTransition; split_ifs <;> norm_num
  · intro x; simp [identityTransition]

theorem transitionCompose_identity_left {X Y : Type*} [Fintype X]
    (R : X → Y → ℝ) : transitionCompose identityTransition R = R := by
  funext x y
  simp [transitionCompose, identityTransition, ite_mul]

theorem transitionCompose_identity_right {X Y : Type*} [Fintype Y]
    (R : X → Y → ℝ) : transitionCompose R identityTransition = R := by
  funext x y
  simp [transitionCompose, identityTransition, mul_ite]

theorem transitionApply_identity {X : Type*} [Fintype X]
    (μ : X → ℝ) : transitionApply μ identityTransition = μ := by
  funext x
  simp [transitionApply,identityTransition,mul_ite]

def transitionWalk {X : Type*} [Fintype X] (R : ℕ → X → X → ℝ)
    (i : ℕ) : ℕ → X → X → ℝ
  | 0 => identityTransition
  | k+1 => transitionCompose (R i) (transitionWalk R (i+1) k)

theorem transitionWalk_isTransition {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (hR : ∀ i, IsTransition (R i)) (i k : ℕ) :
    IsTransition (transitionWalk R i k) := by
  induction k generalizing i with
  | zero => exact identityTransition_isTransition
  | succ k ih => exact transitionCompose_isTransition _ _ (hR i) (ih (i+1))

theorem transitionWalk_one {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i : ℕ) : transitionWalk R i 1 = R i :=
  transitionCompose_identity_right _

theorem transitionWalk_add {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i a b : ℕ) :
    transitionWalk R i (a+b) = transitionCompose (transitionWalk R i a) (transitionWalk R (i+a) b) := by
  induction a generalizing i with
  | zero => simp only [Nat.zero_add,Nat.add_zero,transitionWalk,transitionCompose_identity_left]
  | succ a ih =>
    rw [Nat.succ_add,transitionWalk,ih,transitionWalk,transitionCompose_assoc]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem transitionWalk_stationary {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hπ : ∀ i, transitionApply (π i) (R i) = π (i+1)) (i k : ℕ) :
    transitionApply (π i) (transitionWalk R i k) = π (i+k) := by
  induction k generalizing i with
  | zero => exact transitionApply_identity _
  | succ k ih =>
    rw [transitionWalk,← transitionApply_compose,hπ,ih]
    congr 1 <;> omega

theorem relative_error_propagated_walk {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hR : ∀ i, IsTransition (R i))
    (hπ : ∀ i, transitionApply (π i) (R i) = π (i+1))
    (i k : ℕ) (μ : X → ℝ) (h : ℝ) (he : RelativeError μ (π i) h) :
    RelativeError (transitionApply μ (transitionWalk R i k)) (π (i+k)) h := by
  rw [← transitionWalk_stationary R π hπ i k]
  exact relative_error_preserved _ _ _ _ (transitionWalk_isTransition R hR i k).1 he

theorem relative_error_block_contraction {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hR : ∀ i, IsTransition (R i)) (hπsum : ∀ i, ∑ x, π i x = 1)
    (hπ : ∀ i, transitionApply (π i) (R i) = π (i+1))
    (μ : X → ℝ) (hμ : ∑ x, μ x = 1) (i d q : ℕ) (κ h : ℝ)
    (he : RelativeError μ (π i) h)
    (hminor : ∀ j < q, ∀ x y, κ*π (i+(j+1)*d) y ≤ transitionWalk R (i+j*d) d x y) :
    RelativeError (transitionApply μ (transitionWalk R i (q*d))) (π (i+q*d)) ((1-κ)^q*h) := by
  induction q with
  | zero => simpa [transitionWalk,transitionApply_identity] using he
  | succ q ih =>
    have hprev := ih (fun j hj => hminor j (Nat.lt_succ_of_lt hj))
    let ν := transitionApply μ (transitionWalk R i (q*d))
    have hνsum : ∑ x, ν x = 1 := (transitionApply_total μ _ (transitionWalk_isTransition R hR i (q*d))).trans hμ
    have hstat := transitionWalk_stationary R π hπ (i+q*d) d
    have hstat' : transitionApply (π (i+q*d)) (transitionWalk R (i+q*d) d) = π (i+(q+1)*d) := by
      simpa only [Nat.add_mul, one_mul, Nat.add_assoc] using hstat
    have hc := relative_error_contracted ν (π (i+q*d)) (transitionWalk R (i+q*d) d) κ
      ((1-κ)^q*h) hνsum (hπsum _) (by rw [hstat']; exact hminor q (Nat.lt_succ_self q)) hprev
    rw [hstat',transitionApply_compose] at hc
    have hwalk : transitionCompose (transitionWalk R i (q*d)) (transitionWalk R (i+q*d) d) =
        transitionWalk R i ((q+1)*d) := by rw [Nat.add_mul,one_mul,transitionWalk_add]
    change RelativeError (transitionApply μ (transitionCompose (transitionWalk R i (q*d))
      (transitionWalk R (i+q*d) d))) _ _ at hc
    rw [hwalk] at hc
    convert hc using 1 <;> ring

end Oberwolfach
