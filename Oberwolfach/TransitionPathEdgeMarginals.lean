module

public import Oberwolfach.TransitionPathWeights
public import Oberwolfach.LongReserveEdgeBounds

@[expose] public section

/-! Factorization at a specified edge of a path. The endpoint dependence is
retained, as needed for a reserve prescribed by an arbitrary transport matrix. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem transitionPathWeight_first_edge_test {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i k : ℕ) (g : X → X → X → ℝ) :
    (∑ w : Fin (k+2) → X, transitionPathWeight R i (k+1) w * g (w 0) (w 1) (w (Fin.last (k+1)))) =
      ∑ x, ∑ y, ∑ z, R i x y * transitionWalk R (i+1) k y z * g x y z := by
  rw [sum_fin_tuple_cons]
  simp only [transitionPathWeight,Fin.cons_zero,Fin.cons_one,Fin.tail_cons,Fin.cons_last]
  apply Finset.sum_congr rfl
  intro x _
  have hr (w : Fin (k+1) → X) : R i x (w 0)*transitionPathWeight R (i+1) k w*g x (w 0) (w (Fin.last k)) =
    transitionPathWeight R (i+1) k w * (R i x (w 0)*g x (w 0) (w (Fin.last k))) := by ring
  simp_rw [hr]
  rw [transitionPathWeight_endpoints R (i+1) k (fun y z => R i x y*g x y z)]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem transitionPathWeight_edge_test {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i k : ℕ) (e : Fin k) (g : X → X → X → X → ℝ) :
    (∑ w : Fin (k+1) → X, transitionPathWeight R i k w *
      g (w 0) (w e.castSucc) (w e.succ) (w (Fin.last k))) =
      ∑ x, ∑ v, ∑ w, ∑ z, transitionWalk R i e.val x v * R (i+e.val) v w *
        transitionWalk R (i+e.val+1) (k-e.val-1) w z * g x v w z := by
  induction k generalizing i g with
  | zero => exact e.elim0
  | succ k ih =>
    induction e using Fin.cases with
    | zero =>
      simpa [transitionWalk,identityTransition,ite_mul] using
        transitionPathWeight_first_edge_test R i k (fun x y z => g x x y z)
    | succ e =>
      rw [sum_fin_tuple_cons]
      simp only [transitionPathWeight,Fin.cons_zero,Fin.cons_one,Fin.tail_cons,Fin.cons_last,
        Fin.succ_castSucc,Fin.cons_succ,Fin.val_succ]
      apply Finset.sum_congr rfl
      intro x _
      have hr (w : Fin (k+1) → X) :
        R i x (w 0)*transitionPathWeight R (i+1) k w*g x (w e.castSucc) (w e.succ) (w (Fin.last k)) =
        transitionPathWeight R (i+1) k w *
          (R i x (w 0)*g x (w e.castSucc) (w e.succ) (w (Fin.last k))) := by ring
      change (∑ w : Fin (k+1) → X, R i x (w 0)*transitionPathWeight R (i+1) k w*
        g x (w e.castSucc) (w e.succ) (w (Fin.last k))) = _
      simp_rw [hr]
      rw [ih (i+1) e (fun y v w z => R i x y*g x v w z)]
      have he1 : i+(e.val+1)=i+1+e.val := by omega
      have he2 : k+1-(e.val+1)-1=k-e.val-1 := by omega
      rw [he1,he2,transitionWalk]
      unfold transitionCompose
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      ring

theorem reservedPathWeight_edge_marginal {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (i k : ℕ) (Q : X → X → ℝ) (e : Fin k) (v w : X) :
    (∑ p : Fin (k+1) → X, if p e.castSucc=v ∧ p e.succ=w then reservedPathWeight R i k Q p else 0) =
      reservedEdgeLoad Q (transitionWalk R i e.val) (R (i+e.val))
        (transitionWalk R (i+e.val+1) (k-e.val-1)) (transitionWalk R i k) v w := by
  have hh := transitionPathWeight_edge_test R i k e
    (fun x a b z => if a=v ∧ b=w then Q x z/transitionWalk R i k x z else 0)
  have hleft : (∑ p : Fin (k+1) → X,
      if p e.castSucc=v ∧ p e.succ=w then reservedPathWeight R i k Q p else 0) =
      ∑ p : Fin (k+1) → X, transitionPathWeight R i k p *
        (if p e.castSucc=v ∧ p e.succ=w then Q (p 0) (p (Fin.last k)) /
          transitionWalk R i k (p 0) (p (Fin.last k)) else 0) := by
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp only [reservedPathWeight,mul_zero] <;> ring
  rw [hleft,hh]
  simp [mul_ite,ite_and,reservedEdgeLoad]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  ring

end Oberwolfach
