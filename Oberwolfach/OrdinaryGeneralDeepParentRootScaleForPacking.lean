module

public import Oberwolfach.OrdinaryGeneralDeepParentRootScaleChoiceAnchored

@[expose] public section
/-! After the packing theorem fixes its admissible error, choose the
triangle sampling and edit errors beneath it, before the host is exposed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_deep_parent_root_scale_for_packing
    (r k:ℕ) (hr:4≤r) (hk:4≤k) (α βH c B ω pstar δ h εstar ηcap ζcap:ℝ)
    (hβH:0<βH) (hc:0≤c) (hB:0≤B) (hω:0<ω) (hp:0<pstar)
    (hδ:0<δ) (hδ1:δ<1) (hh:0<h) (hεstar:0<εstar) (hηcap:0<ηcap) (hcap:0<ζcap) (hcapH:ζcap≤h):
    ∃ηH ζ rate lam:ℝ,0<ηH ∧ ηH≤ηcap ∧ 2*ηH<εstar ∧ 0<ζ ∧ 0<rate ∧ 0<lam ∧ ζ≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
    OrdinaryGeneralEditScaleAt r βH ηH B ω pstar (βH/2) (2*ηH) ζ rate N₀ ∧
    OrdinaryUniformDeepRootReferenceAtScale r (by omega) k α (βH/2) c (B/(ω*pstar^(2*r-1)))
      (2*h-ζ) δ (2*ηH) ω ((εstar-2*ηH)/2) lam :=by
  let ηH:=min (εstar/8) (ηcap/2)
  have hη:0<ηH:=by dsimp [ηH];positivity
  have hηsmall:ηH≤ηcap:=by have hh:=min_le_right (εstar/8) (ηcap/2);dsimp [ηH];linarith
  have hgap:0<εstar-2*ηH:=by have hh:=min_le_left (εstar/8) (ηcap/2);dsimp [ηH];linarith
  obtain ⟨ζ,rate,lam,hζ,hrate,hlam,hζcap,N₀,hN₀,hscale,hroot⟩:=
    ordinary_general_deep_parent_root_scale_choice_anchored r k hr hk α βH ηH c B ω pstar δ h ((εstar-2*ηH)/2) ζcap
      hβH hη hc hB hω hp hδ hδ1 hh (by positivity) hcap hcapH
  exact ⟨ηH,ζ,rate,lam,hη,hηsmall,by linarith,hζ,hrate,hlam,hζcap,N₀,hN₀,hscale,hroot⟩
end Oberwolfach
