module

public import Oberwolfach.Concentration

@[expose] public section

/-! Scalar inequalities used to retain the manuscript's Chernoff constants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
namespace Oberwolfach

theorem log_one_add_lower_quadratic {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  let F (y : ℝ) := Real.log (1 + y) - y + y ^ 2 / 2
  have hd (y : ℝ) (hy : y ∈ Icc 0 x) :
      HasDerivAt F (1 / (1 + y) - 1 + y) y := by
    have hn : 1 + y ≠ 0 := ne_of_gt (by linarith [hy.1])
    convert ((((hasDerivAt_id y).const_add 1).log hn).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2) using 1
    · rfl
    · dsimp
      ring
  have hm : MonotoneOn F (Icc 0 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    have hn : 0 < 1 + y := by linarith
    have he : 1 / (1 + y) - 1 + y = y ^ 2 / (1 + y) := by field_simp; ring
    rw [he]
    positivity
  have hh := hm ⟨le_rfl, hx⟩ ⟨hx,le_rfl⟩ hx
  simp only [F, add_zero, Real.log_one, sub_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div] at hh
  linarith

theorem chernoff_upper_entropy {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 / 3 ≤ (1 + x) * Real.log (1 + x) - x := by
  let F (y : ℝ) := (1 + y) * Real.log (1 + y) - y - y ^ 2 / 2 + y ^ 3 / 6
  have hd (y : ℝ) (hy : y ∈ Icc 0 x) :
      HasDerivAt F (Real.log (1 + y) - y + y ^ 2 / 2) y := by
    have hn : 1 + y ≠ 0 := ne_of_gt (by linarith [hy.1])
    convert (((((hasDerivAt_id y).const_add 1).mul
      (((hasDerivAt_id y).const_add 1).log hn)).sub (hasDerivAt_id y)).sub
      (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 3).div_const 6) using 1
    · rfl
    · dsimp
      field_simp [hn]
      ring
  have hm : MonotoneOn F (Icc 0 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    intro y hy
    have h := log_one_add_lower_quadratic (interior_subset hy).1
    linarith
  have hh := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  have hc : x ^ 3 ≤ x ^ 2 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx1)]
  dsimp [F] at hh
  norm_num at hh
  linarith

theorem exp_neg_upper_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let F (y : ℝ) := 1 - y + y ^ 2 / 2 - Real.exp (-y)
  have hd (y : ℝ) : HasDerivAt F (-1 + y + Real.exp (-y)) y := by
    convert (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).sub ((hasDerivAt_id y).neg.exp) using 1
    · rfl
    · dsimp
      ring
  have hm : MonotoneOn F (Icc 0 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).hasDerivWithinAt)
    intro y _
    have h := Real.add_one_le_exp (-y)
    linarith
  have hh := hm ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx
  dsimp [F] at hh
  norm_num at hh
  linarith

end Oberwolfach
