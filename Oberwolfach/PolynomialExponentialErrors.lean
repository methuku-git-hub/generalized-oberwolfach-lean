module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

/-! Combining failure bounds without assuming independence. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Oberwolfach

theorem two_polynomial_exponential_errors_le (n C D a b : ℝ) (i j K : ℕ)
    (hn : 1≤n) (hC : 0≤C) (hD : 0≤D) (hi : i≤K) (hj : j≤K) :
    C*n^i*Real.exp (-a*n)+D*n^j*Real.exp (-b*n)≤
      (C+D)*n^K*Real.exp (-min a b*n) := by
  have hn0 : 0≤n := by linarith
  have hpA : n^i≤n^K := pow_le_pow_right₀ hn hi
  have hpB : n^j≤n^K := pow_le_pow_right₀ hn hj
  have heA : Real.exp (-a*n)≤Real.exp (-min a b*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left a b) hn0
    linarith only [hh]
  have heB : Real.exp (-b*n)≤Real.exp (-min a b*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_right a b) hn0
    linarith only [hh]
  have hA := mul_le_mul (mul_le_mul_of_nonneg_left hpA hC) heA (by positivity)
    (mul_nonneg hC (pow_nonneg hn0 K))
  have hB := mul_le_mul (mul_le_mul_of_nonneg_left hpB hD) heB (by positivity)
    (mul_nonneg hD (pow_nonneg hn0 K))
  nlinarith only [hA,hB]

end Oberwolfach
