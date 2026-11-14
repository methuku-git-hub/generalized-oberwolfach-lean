module

public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! Numerical estimates for a uniform fixed-size step of a vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
noncomputable section
namespace Oberwolfach

theorem eventually_vortex_step_margins {ε : ℝ} (he : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 ≤ n ∧ 2 ≤ ε * n ∧
      (4 * (n : ℝ) / ε) * Real.exp (-ε * (n : ℝ) ^ (1 / 3 : ℝ)) < 1 := by
  obtain ⟨N, hN⟩ := eventually_stretchedExp_le_inv_pow (4 / ε) 1
    (c := ε) (p := 1 / 3) he (by norm_num) 1
  refine ⟨max 2 (max N (Nat.ceil (2 / ε))), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hceil : (Nat.ceil (2 / ε) : ℝ) ≤ n := by exact_mod_cast (show Nat.ceil (2 / ε) ≤ n by omega)
  have he2 : 2 ≤ ε * n := by
    have hh := (Nat.le_ceil (2 / ε)).trans hceil
    have hh' := (div_le_iff₀ he).mp hh
    nlinarith
  refine ⟨hn2, he2, ?_⟩
  have hh := hN n (by omega)
  simp only [Real.rpow_one, pow_one] at hh
  have hsame : (4 * (n : ℝ) / ε) * Real.exp (-ε * (n : ℝ) ^ (1 / 3 : ℝ)) =
      (4 / ε) * n * Real.exp (-ε * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
  rw [hsame]
  exact hh.trans_lt ((div_lt_one (by linarith : (0 : ℝ) < n)).mpr hnreal)

theorem vortex_floor_step_bounds {ε : ℝ} (he1 : ε ≤ 1)
    {n : ℕ} (hlarge : 2 ≤ ε * n) :
    0 < Nat.floor (ε * n) ∧ Nat.floor (ε * n) ≤ n ∧
      ε * n / 2 ≤ (Nat.floor (ε * n) : ℝ) := by
  have hfloor := Nat.floor_le (show 0 ≤ ε * (n : ℝ) by positivity)
  have hfloor' := Nat.lt_floor_add_one (ε * (n : ℝ))
  have hlo : ε * n / 2 ≤ (Nat.floor (ε * n) : ℝ) := by linarith
  have hpos : (0 : ℝ) < Nat.floor (ε * n) := by linarith
  have hn : (Nat.floor (ε * n) : ℝ) ≤ n := by
    have hh := mul_le_mul_of_nonneg_right he1 (show (0 : ℝ) ≤ n by positivity)
    linarith
  exact ⟨by exact_mod_cast hpos, by exact_mod_cast hn, hlo⟩

theorem vortex_normalized_exponent {ε : ℝ} {n r : ℕ}
    (hn : 0 < n) (hr : ε * n / 2 ≤ (r : ℝ)) :
    -2 * (r : ℝ) * ((n : ℝ) ^ (-1 / 3 : ℝ)) ^ 2 ≤
      -ε * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsquare : ((n : ℝ) ^ (-1 / 3 : ℝ)) ^ 2 = (n : ℝ) ^ (-2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    norm_num
  have hprod : (n : ℝ) * (n : ℝ) ^ (-2 / 3 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) := by
    nth_rw 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnpos]
    norm_num
  rw [hsquare]
  have hh := mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hnpos.le (-2 / 3))
  have hmul : ε * n / 2 * (n : ℝ) ^ (-2 / 3 : ℝ) = ε / 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← hprod]
    ring
  rw [hmul] at hh
  linarith

end Oberwolfach
