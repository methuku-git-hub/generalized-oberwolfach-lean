module

public import Oberwolfach.TransitionPathEdgeMarginals
public import Oberwolfach.FinitePathMarginals

@[expose] public section

/-! Normalized transition paths retain every capacity whenever the prescribed
degree distribution propagates along the interval. Only that interval's
balance identities are used. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem transitionWalk_stationary_local {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (d : ℕ → X → ℝ) (i k : ℕ)
    (hbal : ∀ j < k, transitionApply (d (i+j)) (R (i+j))=d (i+j+1)) :
    transitionApply (d i) (transitionWalk R i k)=d (i+k) := by
  induction k generalizing i with
  | zero => exact transitionApply_identity _
  | succ k ih =>
    rw [transitionWalk,← transitionApply_compose]
    have hfirst : transitionApply (d i) (R i)=d (i+1) := by simpa using hbal 0 (by omega)
    rw [hfirst]
    have htail := ih (i+1) (by
      intro j hj
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hbal (j+1) (by omega))
    convert htail using 1 <;> congr 1 <;> omega

def weightedTransitionPath {X : Type*} (μ : X → ℝ) (R : ℕ → X → X → ℝ)
    (i k : ℕ) (w : Fin (k+1) → X) : ℝ := μ (w 0)*transitionPathWeight R i k w

theorem weightedTransitionPath_edge {X : Type*} [Fintype X]
    (μ : X → ℝ) (R : ℕ → X → X → ℝ) (hR : ∀ i, IsTransition (R i))
    (i k : ℕ) (e : Fin k) (v w : X) :
    pathEdgeLoad (weightedTransitionPath μ R i k) e v w =
      transitionApply μ (transitionWalk R i e.val) v * R (i+e.val) v w := by
  have hh := transitionPathWeight_edge_test R i k e
    (fun x a b _ => if a=v ∧ b=w then μ x else 0)
  have hleft : pathEdgeLoad (weightedTransitionPath μ R i k) e v w =
    ∑ p : Fin (k+1) → X, transitionPathWeight R i k p *
      (if p e.castSucc=v ∧ p e.succ=w then μ (p 0) else 0) := by
    unfold pathEdgeLoad weightedTransitionPath
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  rw [hleft,hh]
  simp only [mul_ite,mul_zero,ite_and]
  simp
  have hs := (transitionWalk_isTransition R hR (i+e.val+1) (k-e.val-1)).2 w
  simp_rw [← Finset.sum_mul,← Finset.mul_sum,hs,mul_one]
  unfold transitionApply
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem weightedTransitionPath_total {X : Type*} [Fintype X]
    (μ : X → ℝ) (R : ℕ → X → X → ℝ) (hR : ∀ i, IsTransition (R i))
    (i k : ℕ) : (∑ p, weightedTransitionPath μ R i k p)=∑ x, μ x := by
  have hh := transitionPathWeight_endpoints R i k (fun x _ => μ x)
  have heq : (∑ p, weightedTransitionPath μ R i k p)=
      ∑ p, transitionPathWeight R i k p*μ (p 0) := by
    apply Finset.sum_congr rfl
    intro p _
    exact mul_comm _ _
  rw [heq,hh]
  simp_rw [← Finset.sum_mul,(transitionWalk_isTransition R hR i k).2,one_mul]

theorem weightedTransitionPath_first {X : Type*} [Fintype X]
    (μ : X → ℝ) (R : ℕ → X → X → ℝ) (hR : ∀ i, IsTransition (R i))
    (i k : ℕ) (x : X) : pathVertexLoad (weightedTransitionPath μ R i k) 0 x=μ x := by
  have hh := transitionPathWeight_endpoints R i k (fun a _ => if a=x then μ a else 0)
  have heq : pathVertexLoad (weightedTransitionPath μ R i k) 0 x=
      ∑ p : Fin (k+1) → X, transitionPathWeight R i k p*(if p 0=x then μ (p 0) else 0) := by
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp only [weightedTransitionPath,mul_zero] <;> ring
  rw [heq,hh]
  simp [mul_ite,(transitionWalk_isTransition R hR i k).2,← Finset.sum_mul]

theorem weightedTransitionPath_last {X : Type*} [Fintype X]
    (μ : X → ℝ) (R : ℕ → X → X → ℝ) (i k : ℕ) (z : X) :
    pathVertexLoad (weightedTransitionPath μ R i k) (Fin.last k) z=
      transitionApply μ (transitionWalk R i k) z := by
  have hh := transitionPathWeight_endpoints R i k (fun a b => if b=z then μ a else 0)
  have heq : pathVertexLoad (weightedTransitionPath μ R i k) (Fin.last k) z=
      ∑ p : Fin (k+1) → X, transitionPathWeight R i k p*(if p (Fin.last k)=z then μ (p 0) else 0) := by
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp only [weightedTransitionPath,mul_zero] <;> ring
  rw [heq,hh]
  simp [mul_ite,transitionApply,mul_comm]

end Oberwolfach
