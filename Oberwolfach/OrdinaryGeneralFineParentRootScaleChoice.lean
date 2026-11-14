module

public import Oberwolfach.OrdinaryGeneralParentEditScaleChoiceAnchored
public import Oberwolfach.OrdinaryGeneralParentRootScaleChoice
public import Oberwolfach.OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad

@[expose] public section
/-! Select one actual general-load sharp root reference together with the
parent edit scale before the later, potentially smaller rate is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_fine_parent_root_scale_choice
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (hk:4≤k) (α βH ηH c B ω pstar δ h gap ζcap:ℝ)
    (hβH:0<βH) (hηH:0<ηH) (hc:0≤c) (hB:0≤B) (hω:0<ω) (hp:0<pstar)
    (hδ:0<δ) (hδ1:δ<1) (hh:0<h) (hgap:0<gap) (hcap:0<ζcap) (hcapH:ζcap≤h):
    ∃ζ rate lam:ℝ,0<ζ ∧ 0<rate ∧ 0<lam ∧ ζ≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
    OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B ω pstar (βH/2) (2*ηH) ζ rate N₀ ∧
    OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (by omega) α (βH/2) c
      (B/(ω*pstar^(2*(mWheel+1)-1))) (2*h-ζ) δ (2*ηH) ω gap lam :=by
  obtain ⟨ζ,rate,hζ,hrate,hζcap,hdegree,N₀,hN₀,hscale⟩:=
    ordinary_general_parent_edit_scale_choice_anchored (mWheel+1) βH ηH B ω pstar ζcap hβH hηH hB hω hp hcap
  have hBseed:0≤B/(ω*pstar^(2*(mWheel+1)-1)):=by positivity
  have hcut:0≤2*h-ζ:=by linarith
  obtain ⟨lam,hlam,hroot⟩:=ordinary_uniform_fine_sharp_reference_at_scale_choice_general_load
    mWheel k loadK (by omega) hk α (βH/2) c (B/(ω*pstar^(2*(mWheel+1)-1))) (2*h-ζ) δ (2*ηH) ω gap
    (by positivity) hδ hδ1 hω hgap hBseed hc hcut
  exact ⟨ζ,rate,lam,hζ,hrate,hlam,hζcap,N₀,hN₀,⟨hdegree,hscale⟩,hroot⟩
end Oberwolfach
