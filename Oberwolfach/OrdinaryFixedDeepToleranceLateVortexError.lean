module

public import Oberwolfach.OrdinaryDeepSpacingErrorBeforeLateCap

@[expose] public section
/-! A deep tolerance supplied by the local certificate can be kept fixed;
only its strict hub margin is needed to choose the later vortex error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_fixed_deep_tolerance_late_vortex_error
    (α ε₀ capξ ηHub ξ:ℝ) (hα:0<α) (hε₀:0<ε₀) (hcap:0<capξ) (hgap:ξ<ηHub):
    ∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξ+2*β<ηHub :=by
  intro betaCap hBetaCap
  let β:=min (1/8:ℝ) (min (α/16) (min (ε₀/2) (min (capξ/2) (min ((ηHub-ξ)/4) (betaCap/2)))))
  have hβ:0<β:=by dsimp [β];positivity
  have hβ1:β≤1/8:=min_le_left _ _
  have hβα:β≤α/16:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hβε:β≤ε₀/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hβcap:β≤capξ/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hβgap:β≤(ηHub-ξ)/4:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hβlate:β≤betaCap/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  exact ⟨β,hβ,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem ordinary_certificate_deep_tolerance_hub_gap
    (ε ηHub ξ:ℝ) (hη:0<ηHub) (hε:ε≤ηHub) (hξ:ξ≤ε/100):ξ<ηHub :=by
  linarith
end Oberwolfach
