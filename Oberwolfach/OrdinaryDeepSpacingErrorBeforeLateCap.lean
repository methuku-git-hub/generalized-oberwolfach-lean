module

public import Oberwolfach.OrdinaryDeepSpacingErrorChoices

@[expose] public section
/-! Fix the deep edit tolerance before an additional vortex-error cap is
revealed, then choose the vortex error below that cap without losing margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_spacing_error_before_late_cap
    (α ε₀ cap ηHub:ℝ) (hα:0<α) (hε₀:0<ε₀) (hcap:0<cap) (hη:0<ηHub):
    ∃ξ:ℝ,0<ξ ∧ ξ≤cap ∧ ∀betaCap:ℝ,0<betaCap→∃β:ℝ,
      0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤ε₀ ∧ β≤cap ∧ β≤betaCap ∧ ξ+2*β<ηHub :=by
  let ξ:=min (ηHub/4) (cap/2)
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hξcap:ξ≤cap/2:=min_le_right _ _
  have hξη:ξ≤ηHub/4:=min_le_left _ _
  refine ⟨ξ,hξ,by linarith,?_⟩
  intro betaCap hBetaCap
  let β:=min (1/8:ℝ) (min (α/16) (min (ε₀/2) (min (cap/2) (min (ηHub/8) (betaCap/2)))))
  have hβ:0<β:=by dsimp [β];positivity
  have hβ1:β≤1/8:=min_le_left _ _
  have hβα:β≤α/16:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hβε:β≤ε₀/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hβcap:β≤cap/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hβη:β≤ηHub/8:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hβlate:β≤betaCap/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  exact ⟨β,hβ,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩
end Oberwolfach
