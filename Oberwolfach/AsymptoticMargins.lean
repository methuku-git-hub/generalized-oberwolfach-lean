module

public import Oberwolfach.RandomOrientation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! Explicit asymptotic domination used for probability and routing margins. -/
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem tendsto_polynomial_stretchedExp
    (s : ℝ) {c p : ℝ} (hc : 0 < c) (hp : 0 < p) :
    Tendsto (fun x : ℝ => x ^ s * Real.exp (-c * x ^ p)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / p) c hc).comp
    (tendsto_rpow_atTop hp)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hx]
  congr 2
  field_simp

theorem eventually_stretchedExp_le_inv_pow
    (C K : ℝ) {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (n : ℝ) ^ K * Real.exp (-c * (n : ℝ) ^ p) ≤ 1 / (n : ℝ) ^ q := by
  have ht := ((tendsto_polynomial_stretchedExp (K + q) hc hp).const_mul C).comp
    tendsto_natCast_atTop_atTop
  simp only [mul_zero] at ht
  have hb : ∀ᶠ n : ℕ in atTop,
      C * ((n : ℝ) ^ (K + q) * Real.exp (-c * (n : ℝ) ^ p)) < 1 :=
    ht.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) hn))
  apply (le_div_iff₀ (pow_pos hnpos q)).mpr
  have heq : (C * (n : ℝ) ^ K * Real.exp (-c * (n : ℝ) ^ p)) * (n : ℝ) ^ q =
      C * ((n : ℝ) ^ (K + q) * Real.exp (-c * (n : ℝ) ^ p)) := by
    rw [Real.rpow_add hnpos, Real.rpow_natCast]
    ring
  rw [heq]
  exact (hN n (le_trans (le_max_left _ _) hn)).le

/-- A union bound over all ordered pairs of vertex subsets still decays
faster than every inverse power when each cut has quadratic exponential
failure. The constant and threshold are chosen before the graph order. -/
theorem eventually_allCuts_failure_small {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (4 : ℝ) ^ n * Real.exp (-c * (n : ℝ) ^ 2) ≤ 1 / (n : ℝ) ^ q := by
  obtain ⟨N, hN⟩ := eventually_stretchedExp_le_inv_pow C 0
    (c := c / 2) (p := 2) (by positivity) (by norm_num) q
  refine ⟨max N (Nat.ceil (2 * Real.log 4 / c)), fun n hn => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hceil : (Nat.ceil (2 * Real.log 4 / c) : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_max_right _ _) hn
  have hh : 2 * Real.log 4 / c ≤ (n : ℝ) := (Nat.le_ceil _).trans hceil
  have hlog : 2 * Real.log 4 ≤ (n : ℝ) * c := (div_le_iff₀ hc).mp hh
  have hmul := mul_le_mul_of_nonneg_right hlog hn0
  have hexp : (n : ℝ) * Real.log 4 + -c * (n : ℝ) ^ 2 ≤ -(c / 2) * (n : ℝ) ^ 2 := by
    nlinarith
  have heq : (4 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  calc
    _ = C * Real.exp ((n : ℝ) * Real.log 4 + -c * (n : ℝ) ^ 2) := by
      rw [heq, Real.exp_add]
      ring
    _ ≤ C * Real.exp (-(c / 2) * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
    _ ≤ _ := by
      simpa only [Real.rpow_zero, mul_one, Real.rpow_two] using
        hN n (le_trans (le_max_left _ _) hn)

end Oberwolfach
