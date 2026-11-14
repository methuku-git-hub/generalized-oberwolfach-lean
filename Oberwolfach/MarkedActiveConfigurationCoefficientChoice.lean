module

public import Oberwolfach.MarkedParentConfigurationHierarchy

@[expose] public section
/-! The active configuration coefficient is chosen separately from the
vortex regularity error, after the caller's active coefficient cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_configuration_coefficient_choice
    (βA bC bP βext cap:ℝ)
    (hβA:0<βA) (hC:3*βA≤bC) (hP:3*βA≤bP) (hext:0<βext) (hcap:0<cap):
    ∃ βactive:ℝ,0<βactive ∧ βactive≤βext ∧ βactive≤cap ∧
      3*βactive≤bC ∧ 3*βactive≤bP:=by
  let βactive:=min βA (min βext cap)
  have hβ:0<βactive:=by dsimp [βactive];positivity
  have hA:βactive≤βA:=min_le_left _ _
  have he:βactive≤βext:=(min_le_right _ _).trans (min_le_left _ _)
  have hc:βactive≤cap:=(min_le_right _ _).trans (min_le_right _ _)
  exact ⟨βactive,hβ,he,hc,by linarith,by linarith⟩
end Oberwolfach
