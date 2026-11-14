module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Accumulated normalized errors on geometrically shrinking domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem geometric_chain_sum_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (a : ℕ → ℝ) (k : ℕ) (ha : ∀ i ≤ k, 0 ≤ a i)
    (hstep : ∀ i < k, a i ≤ q * a (i + 1)) :
    ∑ i ∈ Finset.range (k + 1), a i ≤ a k / (1 - q) := by
  induction k with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
    nlinarith [mul_nonneg hq (ha 0 (by omega))]
  | succ k ih =>
    have hh := ih (fun i hi => ha i (by omega)) (fun i hi => hstep i (by omega))
    have hh' := (le_div_iff₀ (by linarith : 0 < 1 - q)).mp hh
    rw [Finset.sum_range_succ]
    apply (le_div_iff₀ (by linarith : 0 < 1 - q)).mpr
    have hlast := hstep k (by omega)
    nlinarith

theorem vortex_negative_power_step {ε x y : ℝ} (he : 0 < ε)
    (hx : 0 < x) (hy : 0 < y) (hstep : y ≤ ε * x) :
    x ^ (-1 / 3 : ℝ) ≤ ε ^ (1 / 3 : ℝ) * y ^ (-1 / 3 : ℝ) := by
  have hh := Real.rpow_le_rpow_of_nonpos hy hstep (by norm_num : (-1 / 3 : ℝ) ≤ 0)
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg he.le (1 / 3))
  have heq : ε ^ (1 / 3 : ℝ) * (ε * x) ^ (-1 / 3 : ℝ) = x ^ (-1 / 3 : ℝ) := by
    rw [Real.mul_rpow he.le hx.le, ← mul_assoc, ← Real.rpow_add he]
    norm_num
  rwa [heq] at hm

theorem vortex_accumulated_error {ε m : ℝ} (he : 0 < ε) (he1 : ε < 1)
    (hm : 0 < m) (n : ℕ → ℝ) (k : ℕ)
    (hn : ∀ i ≤ k, 0 < n i) (hstep : ∀ i < k, n (i + 1) ≤ ε * n i)
    (hfinal : m ≤ n k) :
    ∑ i ∈ Finset.range (k + 1), (n i) ^ (-1 / 3 : ℝ) ≤
      m ^ (-1 / 3 : ℝ) / (1 - ε ^ (1 / 3 : ℝ)) := by
  have hq : 0 ≤ ε ^ (1 / 3 : ℝ) := Real.rpow_nonneg he.le _
  have hq1 : ε ^ (1 / 3 : ℝ) < 1 := by
    have hh := Real.rpow_lt_rpow he.le he1 (by norm_num : (0 : ℝ) < 1 / 3)
    simpa using hh
  have hs := geometric_chain_sum_bound hq hq1 (fun i => (n i) ^ (-1 / 3 : ℝ)) k
    (fun i hi => Real.rpow_nonneg (hn i hi).le _)
    (fun i hi => vortex_negative_power_step he (hn i (by omega)) (hn (i + 1) (by omega)) (hstep i hi))
  exact hs.trans (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hm hfinal (by norm_num)) (by linarith))

end Oberwolfach
