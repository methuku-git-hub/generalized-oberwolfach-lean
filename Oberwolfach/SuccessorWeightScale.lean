module

public import Mathlib.Tactic

@[expose] public section

/-! The exact normalization used in the successor weighting. The tuple
placement probability cancels the powers of the class size in the lower
bound, so that its constant is independent of the approximation error. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def successorPairProbability (m n : ℝ) : ℝ := m ^ 2 / (n * (n - 1))

theorem successorPairProbability_pos {m n : ℝ} (hm : 0 < m) (hn : 1 < n) :
    0 < successorPairProbability m n := by
  unfold successorPairProbability
  positivity

theorem successor_tuple_normalization {c : ℕ} (hc : 2 ≤ c)
    (a m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (a / m ^ (c - 2)) * (m / n) ^ c / successorPairProbability m n =
      (a / n ^ (c - 2)) * ((n - 1) / n) := by
  have hmc : m ^ c = m ^ (c - 2) * m ^ 2 := by rw [← pow_add]; congr 1; omega
  have hnc : n ^ c = n ^ (c - 2) * n ^ 2 := by rw [← pow_add]; congr 1; omega
  unfold successorPairProbability
  rw [div_pow, hmc, hnc]
  field_simp

theorem successor_tuple_normalization_lower {c : ℕ} (hc : 2 ≤ c)
    (a m n : ℝ) (ha : 0 ≤ a) (hm : 0 < m) (hn : 2 ≤ n) :
    a / (2 * n ^ (c - 2)) ≤
      (a / m ^ (c - 2)) * (m / n) ^ c / successorPairProbability m n := by
  have hn0 : 0 < n := by linarith
  rw [successor_tuple_normalization hc a m n hm.ne' hn0.ne']
  have hratio : (1 / 2 : ℝ) ≤ (n - 1) / n := by
    apply (le_div_iff₀ hn0).mpr
    linarith
  have h := mul_le_mul_of_nonneg_left hratio (div_nonneg ha (pow_pos hn0 (c - 2)).le)
  convert h using 1 <;> ring

theorem successor_tuple_normalization_upper {c : ℕ} (hc : 2 ≤ c)
    (C m n K : ℝ) (hC : 0 ≤ C) (hm : 0 < m) (hn : 1 < n)
    (hK : n ≤ K * m) :
    (C / m ^ (c - 2)) / successorPairProbability m n ≤
      C * K ^ c / n ^ (c - 2) := by
  have hn0 : 0 < n := by linarith
  have hmc : m ^ c = m ^ (c - 2) * m ^ 2 := by rw [← pow_add]; congr 1; omega
  have hnc : n ^ c = n ^ (c - 2) * n ^ 2 := by rw [← pow_add]; congr 1; omega
  have hid : (C / m ^ (c - 2)) / successorPairProbability m n =
      (C * (n / m) ^ c / n ^ (c - 2)) * ((n - 1) / n) := by
    unfold successorPairProbability
    rw [div_pow, hnc, hmc]
    field_simp
  rw [hid]
  have hratio : 0 ≤ (n - 1) / n ∧ (n - 1) / n ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_one hn0).mpr; linarith
  have hscale : n / m ≤ K := (div_le_iff₀ hm).mpr hK
  have hp : (n / m) ^ c ≤ K ^ c := pow_le_pow_left₀ (by positivity) hscale _
  calc
    _ ≤ C * (n / m) ^ c / n ^ (c - 2) :=
      mul_le_of_le_one_right (by positivity) hratio.2
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) (by positivity)

theorem successor_positional_normalization (q m n : ℝ) (hm : m ≠ 0) (hn : n ≠ 0) :
    q * (m / n) / successorPairProbability m n = q * (n - 1) / m := by
  unfold successorPairProbability
  field_simp

end Oberwolfach
