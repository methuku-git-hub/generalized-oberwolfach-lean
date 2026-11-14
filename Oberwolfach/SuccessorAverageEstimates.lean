module

public import Oberwolfach.SuccessorDegreeScale

@[expose] public section

/-! Converting the exact averaged positional load to a relative error.
The partition failure and floor losses are kept separate until the final
inequality. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem successor_averaged_position_bounds {n m D s δ ε τ L : ℝ}
    (hn : 1 < n) (hm : 0 < m) (hmn : m ≤ n)
    (hD : n / 2 ≤ D) (hDupper : D ≤ 2 * n)
    (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (harg : 0 ≤ D * m / n - s * m)
    (hδ : δ ≤ ε * successorPairProbability m n)
    (hmargin : s + 1 / m + 2 / n + 2 * ε ≤ τ / 2)
    (hl : (⌊D * m / n - s * m⌋₊ : ℝ) * (m / n - δ) /
      successorPairProbability m n ≤ L)
    (hu : L ≤ (⌊D * m / n - s * m⌋₊ : ℝ) * (m / n) /
      successorPairProbability m n) :
    (1-τ) * D ≤ L ∧ L ≤ D := by
  have hn0 : 0 < n := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hρ := successorPairProbability_pos hm hn
  let q : ℝ := ⌊D * m / n - s * m⌋₊
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq2 : q ≤ 2 * m := by
    have hf := Nat.floor_le harg
    have hd : D * m / n ≤ 2 * m := by
      apply (div_le_iff₀ hn0).mpr
      nlinarith [mul_le_mul_of_nonneg_right hDupper hm.le]
    dsimp [q]
    nlinarith [mul_nonneg hs hm.le]
  have hδq : q * δ / successorPairProbability m n ≤ 2 * n * ε := by
    apply (div_le_iff₀ hρ).mpr
    have hh := mul_le_mul_of_nonneg_left hδ hq0
    have hqn : q ≤ 2 * n := hq2.trans (by linarith)
    have he := mul_le_mul_of_nonneg_right hqn (mul_nonneg hε hρ.le)
    nlinarith
  have hbase := successor_regularized_positional_load hn.le hm hD0 hDupper hs harg
  have hnorm := successor_positional_normalization q m n hm.ne' hn0.ne'
  have hlcalc : q * (m / n - δ) / successorPairProbability m n =
      q * (n-1) / m - q * δ / successorPairProbability m n := by
    rw [mul_sub, sub_div, hnorm]
  change q * (m / n - δ) / successorPairProbability m n ≤ L at hl
  rw [hlcalc] at hl
  change L ≤ q * (m / n) / successorPairProbability m n at hu
  rw [hnorm] at hu
  have herr : s * n + n / m + 2 + 2 * n * ε ≤ τ * n / 2 := by
    have hh := mul_le_mul_of_nonneg_right hmargin hn0.le
    have hc : (2 / n : ℝ) * n = 2 := by field_simp
    rw [add_mul, add_mul, add_mul, hc] at hh
    convert hh using 1 <;> ring
  have hτ : 0 ≤ τ := by
    have hi : 0 ≤ (1 : ℝ) / m := by positivity
    have hj : 0 ≤ (2 : ℝ) / n := by positivity
    linarith
  have hτD := mul_le_mul_of_nonneg_left hD hτ
  constructor
  · have hbl : D - s * n - n / m - 2 ≤ q * (n-1) / m := hbase.1
    nlinarith [hbl]
  · exact hu.trans hbase.2

end Oberwolfach

namespace Oberwolfach

theorem successor_preliminary_tuple_bounds {c : ℕ} (hc : 2 ≤ c)
    (a C p m n K W : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hm : 0 < m) (hn : 2 ≤ n) (hK : n ≤ K * m)
    (hp : (c : ℝ) * p ≤ 1 / 2)
    (hl : (1 - c * p) * (a / m ^ (c - 2)) * (1 / 2) * (m / n) ^ c /
      successorPairProbability m n ≤ W)
    (hu : W ≤ (C / m ^ (c - 2)) / successorPairProbability m n) :
    a / (8 * n ^ (c - 2)) ≤ W ∧ W ≤ C * K ^ c / n ^ (c - 2) := by
  have hn1 : 1 < n := by linarith
  have hρ := successorPairProbability_pos hm hn1
  have hcoef : (a / 4) / m ^ (c - 2) ≤ (1-c*p) * (a / m ^ (c-2)) * (1/2) := by
    have hh := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-c*p by linarith)
      (div_nonneg ha (pow_pos hm (c - 2)).le)
    convert mul_le_mul_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 1/2) using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (m / n) ^ c by positivity)
  have hnorm := successor_tuple_normalization_lower hc (a/4) m n (by positivity) hm hn
  constructor
  · calc
      a / (8 * n ^ (c-2)) = (a/4) / (2 * n ^ (c-2)) := by ring
      _ ≤ _ := hnorm
      _ ≤ _ := div_le_div_of_nonneg_right hmul hρ.le
      _ ≤ W := hl
  · exact hu.trans (successor_tuple_normalization_upper hc C m n K hC hm hn1 hK)

end Oberwolfach
