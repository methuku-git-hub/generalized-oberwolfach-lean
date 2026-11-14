module

public import Oberwolfach.FiniteTransitionWalks
public import Oberwolfach.TransportChainJoint

@[expose] public section

/-! Path probabilities and their exact endpoint and edge marginals. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def transitionPathWeight {X : Type*} (R : ℕ → X → X → ℝ) (i : ℕ) :
    (k : ℕ) → (Fin (k+1) → X) → ℝ
  | 0, _ => 1
  | k+1, w => R i (w 0) (w 1) * transitionPathWeight R (i+1) k (Fin.tail w)

theorem transitionPathWeight_nonneg {X : Type*}
    (R : ℕ → X → X → ℝ) (hR : ∀ i x y, 0 ≤ R i x y)
    (i k : ℕ) (w : Fin (k+1) → X) : 0 ≤ transitionPathWeight R i k w := by
  induction k generalizing i with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (hR i _ _) (ih (i+1) (Fin.tail w))

theorem transitionPathWeight_endpoints {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i k : ℕ) (f : X → X → ℝ) :
    (∑ w : Fin (k+1) → X, transitionPathWeight R i k w * f (w 0) (w (Fin.last k))) =
      ∑ x, ∑ z, transitionWalk R i k x z * f x z := by
  induction k generalizing i f with
  | zero =>
    rw [sum_fin_tuple_one]
    simp [transitionPathWeight,transitionWalk,identityTransition,ite_mul]
  | succ k ih =>
    rw [sum_fin_tuple_cons]
    simp only [transitionPathWeight,Fin.cons_zero,Fin.cons_one,Fin.tail_cons,Fin.cons_last]
    apply Finset.sum_congr rfl
    intro x _
    have hr (w : Fin (k+1) → X) : R i x (w 0)*transitionPathWeight R (i+1) k w*f x (w (Fin.last k)) =
      transitionPathWeight R (i+1) k w*(R i x (w 0)*f x (w (Fin.last k))) := by ring
    simp_rw [hr]
    rw [ih (i+1) (fun y z => R i x y * f x z)]
    simp only [transitionWalk,transitionCompose,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring

theorem transitionPathWeight_endpoint_marginal {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i k : ℕ) (x z : X) :
    (∑ w : Fin (k+1) → X, if w 0=x ∧ w (Fin.last k)=z then transitionPathWeight R i k w else 0) =
      transitionWalk R i k x z := by
  have hh := transitionPathWeight_endpoints R i k (fun a b => if a=x ∧ b=z then 1 else 0)
  simpa [mul_ite,ite_and] using hh

def reservedPathWeight {X : Type*} [Fintype X] (R : ℕ → X → X → ℝ)
    (i k : ℕ) (Q : X → X → ℝ) (w : Fin (k+1) → X) : ℝ :=
  Q (w 0) (w (Fin.last k)) * transitionPathWeight R i k w /
    transitionWalk R i k (w 0) (w (Fin.last k))

theorem reservedPathWeight_nonneg {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (hR : ∀ i, IsTransition (R i))
    (i k : ℕ) (Q : X → X → ℝ) (hQ : ∀ x z, 0 ≤ Q x z) (w : Fin (k+1) → X) :
    0 ≤ reservedPathWeight R i k Q w := by
  exact div_nonneg (mul_nonneg (hQ _ _) (transitionPathWeight_nonneg R (fun i => (hR i).1) i k w))
    ((transitionWalk_isTransition R hR i k).1 _ _)

theorem reservedPathWeight_endpoints {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i k : ℕ) (Q : X → X → ℝ)
    (hT : ∀ x z, 0 < transitionWalk R i k x z) (x z : X) :
    (∑ w : Fin (k+1) → X, if w 0=x ∧ w (Fin.last k)=z then reservedPathWeight R i k Q w else 0) = Q x z := by
  have hh := transitionPathWeight_endpoints R i k
    (fun a b => if a=x ∧ b=z then Q a b / transitionWalk R i k a b else 0)
  have hleft : (∑ w : Fin (k+1) → X,
      if w 0=x ∧ w (Fin.last k)=z then reservedPathWeight R i k Q w else 0) =
      ∑ w : Fin (k+1) → X, transitionPathWeight R i k w *
        (if w 0=x ∧ w (Fin.last k)=z then Q (w 0) (w (Fin.last k)) /
          transitionWalk R i k (w 0) (w (Fin.last k)) else 0) := by
    apply Finset.sum_congr rfl
    intro w _
    split_ifs <;> simp only [reservedPathWeight,mul_zero] <;> ring
  rw [hleft,hh]
  simp [mul_ite,ite_and]
  field_simp [(hT x z).ne']

end Oberwolfach
