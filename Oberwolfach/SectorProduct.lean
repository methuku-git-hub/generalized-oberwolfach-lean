module

public import Oberwolfach.CyclicProducts

@[expose] public section

/-! Exact cancellation of endpoint weights in one distinguished-interval
summand. All divisions cancelled here have explicit nonzero hypotheses. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem sector_product_cancel {I : Type*} [Fintype I] [DecidableEq I]
    (c : I) (H R : I → ℝ) (Q C M : ℝ)
    (hH : ∀ i, i ≠ c → H i ≠ 0) (hQ : Q ≠ 0) (hC : C ≠ 0) (hM : M ≠ 0) :
    ((∏ i ∈ Finset.univ.erase c, H i) / M) *
      (∏ i, if i = c then (Q / C) / Q else R i / H i) =
      (∏ i ∈ Finset.univ.erase c, R i) / (C * M) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => if i = c then (Q / C) / Q else R i / H i) (Finset.mem_univ c)]
  simp only [ite_true]
  have he :
      (∏ i ∈ Finset.univ.erase c, if i = c then (Q / C) / Q else R i / H i) =
        ∏ i ∈ Finset.univ.erase c, R i / H i := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [(Finset.mem_erase.mp hi).1, ite_false]
  rw [he, Finset.prod_div_distrib]
  have hp : (∏ i ∈ Finset.univ.erase c, H i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => hH i (Finset.mem_erase.mp hi).1)
  field_simp

theorem walkTransport_one {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x) (i : I) (x z : X) :
    walkTransport m K s i 1 x z = K i x z := by
  classical
  simp [walkTransport, composeTransport, diagonalTransport, mul_ite, ite_div, (hm (s i) z).ne']

theorem walkTransport_pos {I X : Type*} [Fintype X] [Nonempty X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x) (hK : ∀ i x z, 0 < K i x z)
    (i : I) (j : ℕ) (x z : X) :
    0 < walkTransport m K s i (j + 1) x z := by
  induction j generalizing i x z with
  | zero => rw [walkTransport_one m K s hm]; exact hK i x z
  | succ j ih =>
    change 0 < composeTransport (m (s i)) (K i)
      (walkTransport m K s (s i) (j + 1)) x z
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro y _
    exact div_pos (mul_pos (hK i x y) (ih (s i) y z)) (hm (s i) y)

end Oberwolfach
