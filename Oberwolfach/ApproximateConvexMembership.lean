module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section

/-! Exact membership from uniformly bounded approximation on a neighbourhood.
This is the separation argument used for bounded fractional coefficients. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem functional_unit_ball_maximum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →L[ℝ] ℝ) :
    ∃ z : E, ‖z‖ ≤ 1 ∧ 0 ≤ f z ∧ ∀ e : E, f e ≤ f z * ‖e‖ := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    (show (Metric.closedBall (0 : E) 1).Nonempty from ⟨0, by simp⟩)
    f.continuous.continuousOn
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  have hd : 0 ≤ f z := by simpa using hmax (show (0 : E) ∈ Metric.closedBall 0 1 by simp)
  refine ⟨z, hz', hd, ?_⟩
  intro e
  by_cases he : e = 0
  · simp [he]
  have hepos : 0 < ‖e‖ := norm_pos_iff.mpr he
  have heball : ‖e‖⁻¹ • e ∈ Metric.closedBall (0 : E) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hepos), inv_mul_cancel₀ hepos.ne', le_refl]
  have h := hmax heball
  change f (‖e‖⁻¹ • e) ≤ f z at h
  rw [map_smul, smul_eq_mul] at h
  have hm := mul_le_mul_of_nonneg_left h hepos.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hepos.ne', one_mul, mul_comm] using hm

theorem exact_membership_of_nearby_approximations
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZconv : Convex ℝ Z) (hZclosed : IsClosed Z)
    (w : E) (κ ε : ℝ) (hκ : 0 < κ) (hεκ : ε < κ)
    (happrox : ∀ w' : E, ‖w' - w‖ ≤ κ → ∃ y ∈ Z, ‖y - w'‖ ≤ ε) : w ∈ Z := by
  by_contra hnot
  obtain ⟨f, u, hfu, huf⟩ := geometric_hahn_banach_closed_point hZconv hZclosed hnot
  obtain ⟨z, hz, hd, hbound⟩ := functional_unit_ball_maximum f
  have hnear : ‖(w + κ • z) - w‖ ≤ κ := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hκ]
    nlinarith
  obtain ⟨y, hy, herror⟩ := happrox (w + κ • z) hnear
  have herror' : ‖(w + κ • z) - y‖ ≤ ε := by rwa [norm_sub_rev]
  have hdual := hbound ((w + κ • z) - y)
  rw [map_sub, map_add, map_smul, smul_eq_mul] at hdual
  have hscaled := mul_le_mul_of_nonneg_left herror' hd
  have hpositive := mul_nonneg (le_of_lt (sub_pos.mpr hεκ)) hd
  have hsep := hfu y hy
  nlinarith

end Oberwolfach
