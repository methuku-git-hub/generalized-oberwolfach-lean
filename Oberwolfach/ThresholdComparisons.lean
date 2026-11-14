module

public import Oberwolfach.TwoComponentLower
public import Oberwolfach.OddSharpThreshold
public import Oberwolfach.FourSharpThreshold

@[expose] public section

/-! The ordinary-threshold comparisons used by cycle factors and transformers. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def cycleFactorDensity (r : ℕ) : ℝ :=
  if Even r then 1 / 2 else 1 / 2 + 1 / (2 * r)

def transformerDensity (r : ℕ) : ℝ :=
  if r = 3 then 3 / 4 else if r = 4 then 2 / 3 else cycleFactorDensity r

def ordinaryCycleLowerDensity (r : ℕ) : ℝ :=
  if r = 4 then 2 / 3 else if Even r then 1 / 2 else 1 / 2 + 1 / (2 * r - 2)

theorem cycleFactorDensity_half_le (r : ℕ) : (1 / 2 : ℝ) ≤ cycleFactorDensity r := by
  unfold cycleFactorDensity
  split_ifs
  · exact le_refl _
  · have hh : (0 : ℝ) ≤ 1 / (2 * r) := by positivity
    linarith

theorem cycleFactorDensity_le_transformerDensity (r : ℕ) :
    cycleFactorDensity r ≤ transformerDensity r := by
  unfold transformerDensity
  split_ifs with h3 h4
  · subst r
    norm_num [cycleFactorDensity]
  · subst r
    norm_num [cycleFactorDensity]
  · exact le_refl _

theorem cycleThreshold_ge_cycleFactorDensity {r : ℕ} (hr : 3 ≤ r) :
    cycleFactorDensity r ≤ cycleThreshold r := by
  by_cases he : Even r
  · simpa only [cycleFactorDensity, he, ite_true, ite_false] using cycleThreshold_half_le hr
  · have hodd : Odd r := Nat.not_even_iff_odd.mp he
    have hh := cycleThreshold_odd_sharp_lower hr hodd
    have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hd : (0 : ℝ) < 2 * r - 2 := by linarith
    have hid : (r : ℝ) / (2 * r - 2) = 1 / 2 + 1 / (2 * r - 2) := by
      apply (div_eq_iff hd.ne').mpr
      rw [add_mul, div_mul_cancel₀ _ hd.ne']
      ring
    rw [hid] at hh
    have hc := one_div_le_one_div_of_le hd (by linarith : (2 : ℝ) * r - 2 ≤ 2 * r)
    simp only [cycleFactorDensity, he, ite_false]
    linarith

theorem cycleThreshold_ge_transformerDensity {r : ℕ} (hr : 3 ≤ r) :
    transformerDensity r ≤ cycleThreshold r := by
  unfold transformerDensity
  split_ifs with h3 h4
  · subst r
    exact cycleThreshold_triangle_lower
  · subst r
    exact cycleThreshold_four_lower
  · exact cycleThreshold_ge_cycleFactorDensity hr

theorem cycleThreshold_ge_ordinaryCycleLowerDensity {r : ℕ} (hr : 3 ≤ r) :
    ordinaryCycleLowerDensity r ≤ cycleThreshold r := by
  unfold ordinaryCycleLowerDensity
  split_ifs with h4 he
  · subst r
    exact cycleThreshold_four_lower
  · exact cycleThreshold_half_le hr
  · have hh := cycleThreshold_odd_sharp_lower hr (Nat.not_even_iff_odd.mp he)
    have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hd : (0 : ℝ) < 2 * r - 2 := by linarith
    have hid : (r : ℝ) / (2 * r - 2) = 1 / 2 + 1 / (2 * r - 2) := by
      apply (div_eq_iff hd.ne').mpr
      rw [add_mul, div_mul_cancel₀ _ hd.ne']
      ring
    rwa [hid] at hh

end Oberwolfach
