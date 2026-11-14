module

public import Oberwolfach.OrdinaryDeepRowsCutsAfterEarly

@[expose] public section
/-! Positive spacing and vortex errors can be chosen below an arbitrary
previously fixed cap while leaving the strict hub margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_spacing_error_choices
    (α ε₀ cap ηHub:ℝ) (hα:0<α) (hε₀:0<ε₀) (hcap:0<cap) (hη:0<ηHub):
    ∃ξ β:ℝ,0<ξ ∧ ξ≤cap ∧ 0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤ε₀ ∧ β≤cap ∧ ξ+2*β<ηHub :=by
  let ξ:=min (ηHub/4) (cap/2)
  let β:=min (1/8:ℝ) (min (α/16) (min (ε₀/2) (min (cap/2) (ηHub/8))))
  have hξ:0<ξ:=by dsimp [ξ]; positivity
  have hβ:0<β:=by dsimp [β]; positivity
  have hξcap:ξ≤cap/2:=min_le_right _ _
  have hξη:ξ≤ηHub/4:=min_le_left _ _
  have hβ1:β≤1/8:=min_le_left _ _
  have hβα:β≤α/16:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hβε:β≤ε₀/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hβcap:β≤cap/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hβη:β≤ηHub/8:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  exact ⟨ξ,β,hξ,by linarith,hβ,by linarith,by linarith,by linarith,by linarith,by linarith⟩
end Oberwolfach
