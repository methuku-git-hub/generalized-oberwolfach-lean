module

public import Oberwolfach.OrdinaryGeneralParentRootScaleChoice

@[expose] public section
/-! A parent edit estimate remains valid when a later selector uses a
smaller nonnegative rate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_general_edit_scale_rate_monotone
    (r:ℕ) (βH ηH B ω pstar βparent εparent ζ rateSmall rateLarge:ℝ) (N₀:ℕ)
    (hrate:rateSmall≤rateLarge)
    (h:OrdinaryGeneralEditScaleAt r βH ηH B ω pstar βparent εparent ζ rateLarge N₀):
    OrdinaryGeneralEditScaleAt r βH ηH B ω pstar βparent εparent ζ rateSmall N₀ :=by
  refine ⟨h.1,?_⟩
  intro N U L hN hU hL hrateSmall
  have hN0:0≤N:=(Nat.cast_nonneg N₀).trans hN
  exact h.2 N U L hN hU hL (hrateSmall.trans (mul_le_mul_of_nonneg_right hrate hN0))
end Oberwolfach
