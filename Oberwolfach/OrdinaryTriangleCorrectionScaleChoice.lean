module

public import Oberwolfach.OrdinaryTriangleSeparatedNumericScales

@[expose] public section
/-! Choose the correction error only after the vortex and load scales. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_correction_scale_choice
    (ε a cap δrate:ℝ) (hε:0<ε) (ha:0<a) (hcap:0<cap) (hδrate:0<δrate):
    ∃ξ:ℝ,0<ξ ∧ ξ≤cap ∧ ξ≤ε/100 ∧ 80*ξ≤a^2 ∧ 10*ξ≤δrate :=by
  let ξ:=min cap (min (ε/100) (min (a^2/80) (δrate/10)))
  have hξ:0<ξ:=by dsimp [ξ]; positivity
  have h1:ξ≤cap:=min_le_left _ _
  have h2:ξ≤ε/100:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:ξ≤a^2/80:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:ξ≤δrate/10:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ξ,hξ,h1,h2,?_,?_⟩ <;> linarith
end Oberwolfach
