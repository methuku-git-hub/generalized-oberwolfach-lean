module

public import Oberwolfach.OrdinaryParentCleanupMarginChoices

@[expose] public section
/-! Cap the later contraction simultaneously by the user's bound, the
placement and absorber scales, and the already chosen hub tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_scale_before_failure
    (εmax εearly capInner ηHub aDeep ρ₀:ℝ)
    (hmax:0<εmax) (hearly:0<εearly) (hinner:0<capInner) (hη:0<ηHub) (ha:0<aDeep) (hρ:0<ρ₀):
    ∃εcap:ℝ,0<εcap ∧ εcap≤εmax ∧ εcap≤εearly ∧ εcap≤capInner ∧
      εcap≤ηHub ∧ εcap≤aDeep ∧ εcap≤ρ₀/16 :=by
  let εcap:=min εmax (min εearly (min capInner (min ηHub (min aDeep (ρ₀/16)))))
  have hcap:0<εcap:=by dsimp [εcap];positivity
  exact ⟨εcap,hcap,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))⟩
end Oberwolfach
