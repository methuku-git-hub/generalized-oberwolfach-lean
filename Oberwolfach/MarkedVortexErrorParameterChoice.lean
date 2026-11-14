module

public import Oberwolfach.MarkedJointRecordErrorChoice

@[expose] public section
/-! Choose the vortex regularity error after the sampling threshold, without
identifying it with the active configuration coefficient. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_error_parameter_choice
    (α κ x βmax:ℝ) (hα:0<α) (hκ:0<κ) (hx:0<x) (hmax:0<βmax):
    ∃ β:ℝ,0<β ∧ β≤βmax ∧ β≤(κ/4)/4 ∧ β≤κ ∧ β≤x ∧
      β≤α/8 ∧ β≤3*α/40 ∧ β≤1/4 ∧ β≤3/20:=by
  let β:=min βmax (min (κ/32) (min x (min (3*α/80) (3/40))))
  have hβ:0<β:=by dsimp [β];positivity
  have hmax':β≤βmax:=min_le_left _ _
  have hκ':β≤κ/32:=(min_le_right _ _).trans (min_le_left _ _)
  have hx':β≤x:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hα':β≤3*α/80:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h1:β≤3/40:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨β,hβ,hmax',?_,?_,hx',?_,?_,?_,?_⟩ <;> linarith
end Oberwolfach
