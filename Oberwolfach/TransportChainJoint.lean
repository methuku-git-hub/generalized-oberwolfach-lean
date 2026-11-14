module

public import Oberwolfach.TransportFixedPoint
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Explicit joint weights on a chain of transportation matrices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sum_fin_tuple_cons {X : Type*} [Fintype X] {n : ℕ}
    (f : (Fin (n + 1) → X) → ℝ) :
    (∑ w, f w) = ∑ x, ∑ v : Fin n → X, f (Fin.cons x v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => X)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_fin_tuple_one {X : Type*} [Fintype X]
    (f : (Fin 1 → X) → ℝ) :
    (∑ w, f w) = ∑ x, f (fun _ => x) := by
  rw [← (Equiv.funUnique (Fin 1) X).symm.sum_comp]
  rfl

def chainJoint {I X : Type*}
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I) (i : I) :
    (j : ℕ) → (Fin (j + 1) → X) → ℝ
  | 0, w => m i (w 0)
  | j + 1, w =>
      K i (w 0) (w 1) / m (s i) (w 1) *
        chainJoint m K s (s i) j (Fin.tail w)

theorem chainJoint_nonneg {I X : Type*}
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 ≤ m i x) (hK : ∀ i x y, 0 ≤ K i x y)
    (i : I) (j : ℕ) (w : Fin (j + 1) → X) :
    0 ≤ chainJoint m K s i j w := by
  induction j generalizing i with
  | zero => exact hm i (w 0)
  | succ j ih =>
    exact mul_nonneg (div_nonneg (hK i (w 0) (w 1)) (hm (s i) (w 1)))
      (ih (s i) (Fin.tail w))

theorem chainJoint_endpoints {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (i : I) (j : ℕ) (f : X → X → ℝ) :
    (∑ w : Fin (j + 1) → X,
      chainJoint m K s i j w * f (w 0) (w (Fin.last j))) =
      ∑ x, ∑ z, walkTransport m K s i j x z * f x z := by
  induction j generalizing i f with
  | zero =>
    rw [sum_fin_tuple_one]
    simp [chainJoint, walkTransport, diagonalTransport, ite_mul]
  | succ j ih =>
    rw [sum_fin_tuple_cons]
    simp only [chainJoint, Fin.cons_zero, Fin.cons_one, Fin.tail_cons, Fin.cons_last]
    apply Finset.sum_congr rfl
    intro x hx
    have heq (v : Fin (j + 1) → X) :
        K i x (v 0) / m (s i) (v 0) * chainJoint m K s (s i) j v *
          f x (v (Fin.last j)) =
        chainJoint m K s (s i) j v *
          (K i x (v 0) / m (s i) (v 0) * f x (v (Fin.last j))) := by ring
    simp_rw [heq]
    rw [ih (s i) (fun y z => K i x y / m (s i) y * f x z)]
    change _ = ∑ z, composeTransport (m (s i)) (K i) (walkTransport m K s (s i) j) x z * f x z
    unfold composeTransport
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    ring

theorem chainJoint_first {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (s i)))
    (i : I) (j : ℕ) (f : X → ℝ) :
    (∑ w : Fin (j + 1) → X, chainJoint m K s i j w * f (w 0)) =
      ∑ x, m i x * f x := by
  rw [chainJoint_endpoints m K s i j (fun x _ => f x)]
  simp_rw [← Finset.sum_mul, (walkTransport_mem m K s hm hK i j).2.1]

theorem chainJoint_total {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (s i)))
    (i : I) (j : ℕ) :
    (∑ w : Fin (j + 1) → X, chainJoint m K s i j w) = ∑ x, m i x := by
  simpa only [mul_one] using chainJoint_first m K s hm hK i j (fun _ => 1)

theorem chainJoint_tail {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (s i)))
    (i : I) (j : ℕ) (f : (Fin (j + 1) → X) → ℝ) :
    (∑ w : Fin (j + 2) → X, chainJoint m K s i (j + 1) w * f (Fin.tail w)) =
      ∑ v : Fin (j + 1) → X, chainJoint m K s (s i) j v * f v := by
  rw [sum_fin_tuple_cons]
  simp only [chainJoint, Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div,
    (hK i).2.2, div_self (hm (s i) (v 0)).ne', one_mul]

theorem chainJoint_first_pair {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (s i)))
    (i : I) (j : ℕ) (f : X → X → ℝ) :
    (∑ w : Fin (j + 2) → X, chainJoint m K s i (j + 1) w * f (w 0) (w 1)) =
      ∑ x, ∑ y, K i x y * f x y := by
  rw [sum_fin_tuple_cons]
  simp only [chainJoint, Fin.cons_zero, Fin.cons_one, Fin.tail_cons]
  apply Finset.sum_congr rfl
  intro x hx
  have heq (v : Fin (j + 1) → X) :
      K i x (v 0) / m (s i) (v 0) * chainJoint m K s (s i) j v * f x (v 0) =
      chainJoint m K s (s i) j v * (K i x (v 0) / m (s i) (v 0) * f x (v 0)) := by ring
  simp_rw [heq]
  rw [chainJoint_first m K s hm hK (s i) j (fun y => K i x y / m (s i) y * f x y)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← mul_assoc, mul_div_cancel₀ _ (hm (s i) y).ne']

theorem chainJoint_pair {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (s i)))
    (i : I) (j : ℕ) (e : Fin j) (f : X → X → ℝ) :
    (∑ w : Fin (j + 1) → X,
      chainJoint m K s i j w * f (w e.castSucc) (w e.succ)) =
      ∑ x, ∑ y, K (s^[e.val] i) x y * f x y := by
  induction j generalizing i with
  | zero => exact e.elim0
  | succ j ih =>
    induction e using Fin.cases with
    | zero =>
      have h01 : (Fin.succ (0 : Fin (j + 1))) = (1 : Fin (j + 2)) := by ext; simp
      simpa only [Fin.castSucc_zero, h01, Fin.val_zero, Function.iterate_zero_apply] using
        chainJoint_first_pair m K s hm hK i j f
    | succ e =>
      change (∑ w : Fin (j + 2) → X,
        chainJoint m K s i (j + 1) w *
          (fun v : Fin (j + 1) → X => f (v e.castSucc) (v e.succ)) (Fin.tail w)) = _
      rw [chainJoint_tail m K s hm hK i j (fun v => f (v e.castSucc) (v e.succ))]
      simpa only [Fin.val_succ, Function.iterate_succ_apply] using ih (s i) e

theorem chainJoint_endpoint_marginal {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (i : I) (j : ℕ) (x z : X) :
    (∑ w : Fin (j + 1) → X,
      if w 0 = x ∧ w (Fin.last j) = z then chainJoint m K s i j w else 0) =
      walkTransport m K s i j x z := by
  have hh := chainJoint_endpoints m K s i j (fun a b => if a = x ∧ b = z then 1 else 0)
  simpa [mul_ite, ite_and] using hh

theorem chainJoint_pair_marginal {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (s i)))
    (i : I) (j : ℕ) (e : Fin j) (x y : X) :
    (∑ w : Fin (j + 1) → X,
      if w e.castSucc = x ∧ w e.succ = y then chainJoint m K s i j w else 0) =
      K (s^[e.val] i) x y := by
  have hh := chainJoint_pair m K s hm hK i j e (fun a b => if a = x ∧ b = y then 1 else 0)
  simpa [mul_ite, ite_and] using hh

end Oberwolfach
