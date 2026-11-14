module

public import Oberwolfach.OrdinaryGeneralDeepParentRootScaleForPacking
public import Oberwolfach.OrdinaryVortexBufferedRootGeometryQuantitativeSlackOrderedNamed

@[expose] public section
/-! Synchronize the selected packing error, triangle reference margin and
actual root-cover geometry in pre-host order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_deep_packing_before_quantitative_buffered_geometry
    (mWheel k buffer:ℕ) (hbuffer:2≤buffer) (hm:3≤mWheel) (hk:4≤k) (α:ℝ) (εstar:ℝ) (hεstar:0<εstar)
    (ρ₀ βH c B pstar δ h ηcap ζcap geomcap:ℝ)
    (hρ₀:0<ρ₀) (hβH:0<βH) (hc:0<c) (hB:0<B) (hp:0<pstar)
    (hδ:0<δ) (hδ1:δ<1/4) (hh:0<h) (hηcap:0<ηcap)
    (hζcap:0<ζcap) (hζsmall:ζcap≤h/8) (hgeomcap:0<geomcap) (hgeomsmall:geomcap≤h/8):
    let ω:=ρ₀/16;
    let Bseed:=B/(ω*pstar^(2*(mWheel+1)-1));
    ∃ηH ζparent rate lam:ℝ,0<ηH ∧ ηH≤ηcap ∧ 2*ηH<εstar ∧ 0<ζparent ∧ 0<rate ∧ 0<lam ∧ ζparent≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
    OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B ω pstar (βH/2) (2*ηH) ζparent rate N₀ ∧
    OrdinaryUniformDeepRootReferenceAtScale (mWheel+1) (by omega) k α (βH/2) c Bseed (2*h-ζparent) δ (2*ηH) ω
      ((εstar-2*ηH)/2) lam ∧
    ∃βout ξ ζ cGeom:ℝ,0<βout ∧ βout=βH/8 ∧ 0<ξ ∧ 0<ζ ∧ 0<cGeom ∧
      ξ≤geomcap ∧ ζ≤geomcap ∧ h/2≤(2*h-ζparent)-ξ-ζ ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧ cGeom*min 1 η≤γ ∧
    OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale mWheel k buffer ρ₀ (βH/4) (c*(1-δ)^((mWheel+1)-1)) Bseed
      (2*ηH+(εstar-2*ηH)/2) ((εstar-2*ηH)/2) η βout ξ ζ p eps γ :=by
  intro ω Bseed
  have hω:0<ω:=by dsimp [ω];positivity
  have hζh:ζcap≤h:=by linarith
  obtain ⟨ηH,ζparent,rate,lam,hηH,hηHcap,hηHstar,hζparent,hrate,hlam,hζcap',N₀,hN₀,hscale,hroot⟩:=
    ordinary_general_deep_parent_root_scale_for_packing (mWheel+1) k (by omega) hk α βH c B ω pstar δ h εstar ηcap ζcap
      hβH hc.le hB.le hω hp hδ (by linarith) hh hεstar hηcap hζcap hζh
  have hgap:0<(εstar-2*ηH)/2:=by linarith
  have hb:0<c*(1-δ)^((mWheel+1)-1):=mul_pos hc (pow_pos (by linarith) _)
  have hBseed:0≤Bseed:=by dsimp [Bseed];positivity
  obtain ⟨βout,ξ,ζ,cGeom,hβout,hβeq,hξ,hζ,hξcap,hζoutcap,hcGeom,hgeo⟩:=
    ordinary_vortex_buffered_general_root_geometry_quantitative_slack_ordered_named mWheel k buffer hbuffer ρ₀ (βH/4) (c*(1-δ)^((mWheel+1)-1)) Bseed
      (2*ηH+(εstar-2*ηH)/2) ((εstar-2*ηH)/2) geomcap
      hk hρ₀ (by positivity) hb hBseed hgap hgeomcap
  have hβeq':βout=βH/8:=by linarith
  have hcut:h/2≤(2*h-ζparent)-ξ-ζ:=by linarith
  exact ⟨ηH,ζparent,rate,lam,hηH,hηHcap,hηHstar,hζparent,hrate,hlam,hζcap',N₀,hN₀,hscale,hroot,
    βout,ξ,ζ,cGeom,hβout,hβeq',hξ,hζ,hcGeom,hξcap,hζoutcap,hcut,hgeo⟩
end Oberwolfach
