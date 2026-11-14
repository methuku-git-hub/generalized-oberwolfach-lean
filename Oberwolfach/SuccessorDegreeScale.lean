module

public import Oberwolfach.SuccessorWeightScale

@[expose] public section

/-! Floor losses and positional-load estimates for the common regularized
degree. The approximation parameter is chosen before the order threshold. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem successor_regularized_degree_lower {n m D s q β ε : ℝ}
    (hn : 0 < n) (hm : 0 < m)
    (hD : (q + β - ε) * n ≤ D)
    (hmargin : ε + s + 1 / m ≤ β / 2) :
    (q + β / 2) * m ≤ (⌊D * m / n - s * m⌋₊ : ℝ) := by
  have hd : (q + β - ε) * m ≤ D * m / n := by
    apply (le_div_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_right hD hm.le]
  have herr := mul_le_mul_of_nonneg_right hmargin hm.le
  have hcancel : (1 / m : ℝ) * m = 1 := by field_simp
  have hf := Nat.lt_floor_add_one (D * m / n - s * m)
  rw [add_mul, add_mul, hcancel] at herr
  linarith

theorem successor_regularized_positional_load {n m D s : ℝ}
    (hn : 1 ≤ n) (hm : 0 < m) (hD : 0 ≤ D) (hDupper : D ≤ 2 * n)
    (hs : 0 ≤ s) (harg : 0 ≤ D * m / n - s * m) :
    D - s * n - n / m - 2 ≤ (⌊D * m / n - s * m⌋₊ : ℝ) * (n - 1) / m ∧
      (⌊D * m / n - s * m⌋₊ : ℝ) * (n - 1) / m ≤ D := by
  have hn0 : 0 < n := by linarith
  have hscale : 0 ≤ (n - 1) / m := div_nonneg (by linarith) hm.le
  have hlo := (Nat.lt_floor_add_one (D * m / n - s * m)).le
  have hhi := Nat.floor_le harg
  have hlow : (D * m / n - s * m - 1) * ((n - 1) / m) ≤
      (⌊D * m / n - s * m⌋₊ : ℝ) * ((n - 1) / m) :=
    mul_le_mul_of_nonneg_right (by linarith) hscale
  have hupper : (⌊D * m / n - s * m⌋₊ : ℝ) * ((n - 1) / m) ≤
      (D * m / n) * ((n - 1) / m) :=
    mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hs hm.le]) hscale
  have hloweq : (D * m / n - s * m - 1) * ((n - 1) / m) =
      D - D / n - s * n + s - n / m + 1 / m := by field_simp; ring
  have hupeq : (D * m / n) * ((n - 1) / m) = D - D / n := by field_simp
  rw [hloweq, ← mul_div_assoc] at hlow
  rw [hupeq, ← mul_div_assoc] at hupper
  have hD2 : D / n ≤ 2 := (div_le_iff₀ hn0).mpr hDupper
  have hD0 : 0 ≤ D / n := div_nonneg hD hn0.le
  have hmInv : 0 ≤ (1 : ℝ) / m := by positivity
  constructor <;> linarith

end Oberwolfach
