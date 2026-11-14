module

public import Oberwolfach.MarkedVortexInnerCutFieldsUniform

@[expose] public section
/-! Choose inner-cut parameters using fixed density lower bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem marked_uniform_inner_cut_parameter_choice
    (α kstar tstar ζ δcap hcap:ℝ)
    (hα:0<α) (hk:0<kstar) (ht:0<tstar) (hζ:ζ≤tstar/16)
    (hδcap:0<δcap) (hhcap:0<hcap):
    ∃ δ h:ℝ,0<δ ∧ δ≤δcap ∧ 0<h ∧ h≤hcap ∧
      δ≤α/32 ∧ δ≤kstar/32 ∧ 2*δ≤tstar/8 ∧
      h≤α*kstar/4 ∧ h≤tstar/8-ζ:=by
  let b:=min α (min kstar tstar)
  have hb:0<b:=by dsimp [b];positivity
  have hbα:b≤α:=min_le_left _ _
  have hbk:b≤kstar:=(min_le_right _ _).trans (min_le_left _ _)
  have hbt:b≤tstar:=(min_le_right _ _).trans (min_le_right _ _)
  let δ:=min δcap (b/256)
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδcap':δ≤δcap:=min_le_left _ _
  have hδb:δ≤b/256:=min_le_right _ _
  let v:=min hcap (min (α*kstar/4) (tstar/16))
  have hv:0<v:=by dsimp [v];positivity
  have hvcap:v≤hcap:=min_le_left _ _
  have hvprod:v≤α*kstar/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hvt:v≤tstar/16:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,v/2,hδ,hδcap',by positivity,?_,?_,?_,?_,?_,?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
end Oberwolfach
