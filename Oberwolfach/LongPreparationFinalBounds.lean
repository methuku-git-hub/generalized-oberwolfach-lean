module

public import Mathlib.Tactic

@[expose] public section

/-! Numerical closure for a long-preparation probability after its sample
    and protected set have been selected. -/
set_option autoImplicit false
namespace Oberwolfach

theorem long_preparation_final_bounds
    {n : ℕ} (I : Finset (Fin n)) (ε εmax χ failure probability : ℝ)
    (hsize : (I.card : ℝ) ≤ ε * n) (hε : ε ≤ εmax)
    (hfailure : failure ≤ χ) (hprob : 1 - failure ≤ probability) :
    (I.card : ℝ) ≤ εmax * n ∧ 1 - χ - 1 / (n : ℝ) ^ 10 ≤ probability := by
  constructor
  · exact hsize.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg n))
  · have hnonneg : 0 ≤ 1 / (n : ℝ) ^ 10 := by positivity
    linarith only [hfailure, hprob, hnonneg]

end Oberwolfach
