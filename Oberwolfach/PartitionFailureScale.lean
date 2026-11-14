module

public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! The explicit failure probability for all ordinary and successor
neighbourhood tests tends to zero at a rate uniform in the graph and
permutation. The cycle count and η are fixed before the order threshold. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem equal_cell_size_bounds (n c : ℕ) (hc : 0 < c) (hcn : c ≤ n) :
    0 < n / c ∧ n ≤ 2 * c * (n / c) ∧ c * (n / c) ≤ n := by
  have hm : 0 < n / c := Nat.div_pos hcn hc
  have he := Nat.mod_add_div n c
  have hr := Nat.mod_lt n hc
  have hmul : c ≤ c * (n / c) := by nlinarith
  refine ⟨hm, ?_, ?_⟩
  · nlinarith
  · omega

def partitionFailure (c : ℕ) (η : ℝ) (n : ℕ) : ℝ :=
  4 * c * n * Real.exp (-η ^ 2 * (n / c : ℕ) / 2)

theorem partition_failure_eventually_small (c : ℕ) (hc : 0 < c)
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < n / c ∧ n ≤ 2 * c * (n / c) ∧ partitionFailure c η n ≤ 1 / (n : ℝ) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hκ : 0 < η ^ 2 / (4 * c) := by positivity
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow (4 * c) 1
    (c := η ^ 2 / (4 * c)) (p := 1) hκ (by norm_num) 1
  refine ⟨max N c, ?_⟩
  intro n hn
  have hnc : c ≤ n := (le_max_right _ _).trans hn
  obtain ⟨hm, hscale, _⟩ := equal_cell_size_bounds n c hc hnc
  refine ⟨hm, hscale, ?_⟩
  have hscaler : (n : ℝ) ≤ 2 * c * (n / c : ℕ) := by exact_mod_cast hscale
  have hexp : -η ^ 2 * (n / c : ℕ) / 2 ≤ -(η ^ 2 / (4 * c)) * n := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 4 * c by positivity)).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hscaler (sq_nonneg η)]
  calc
    partitionFailure c η n ≤ 4 * c * n * Real.exp (-(η ^ 2 / (4 * c)) * n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ ≤ _ := by
      simpa only [Real.rpow_one, pow_one] using hN n ((le_max_left _ _).trans hn)

end Oberwolfach
