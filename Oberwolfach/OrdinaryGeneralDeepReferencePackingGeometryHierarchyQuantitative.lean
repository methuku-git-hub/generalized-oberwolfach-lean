module

public import Oberwolfach.OrdinaryGeneralDeepReferenceCapacityHierarchyQuantitative
public import Oberwolfach.OrdinaryGeneralDeepPackingBeforeBalanceGeometry

@[expose] public section
/-! Choose compatible general-wheel reference, packing and vortex geometry
    parameters before the later pairing and finite-host choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_deep_reference_packing_geometry_hierarchy_quantitative
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pstar ηP:ℝ) (hα:0<α) (hα1:α≤1/2)
    (hθ1:max (1/2) (cycleThreshold (m+1))+α/2≤1)
    (hρ₀:0<ρ₀) (hp:0<pstar) (hp1:pstar≤1) (hηP:0<ηP):
    ∃(δ h βP row:ℝ) (k:ℕ) (βH c B εstar cLinear:ℝ),
      0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<βP ∧ 0<row ∧ m+3≤k ∧
      0<βH ∧ 0<c ∧ 0<B ∧ 0<εstar ∧ 0<cLinear ∧
      OrdinaryGeneralDeepSafeCapacityRuleQuantitative m k hm α (ρ₀/16) (βH/8)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εstar cLinear ∧
    ∀ηcap:ℝ,0<ηcap→
    ∃ηH ζparent rate lam:ℝ,0<ηH ∧ ηH≤ηcap ∧ 2*ηH<εstar ∧
      0<ζparent ∧ 0<rate ∧ 0<lam ∧ ζparent≤h/16 ∧
    ∃N₀:ℕ,1≤N₀ ∧
    OrdinaryGeneralEditScaleAt (m+1) βH ηH B (ρ₀/16) pstar (βH/2) (2*ηH) ζparent rate N₀ ∧
    OrdinaryUniformDeepRootReferenceAtScale (m+1) (by omega) k α (βH/2) c
      (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*h-ζparent) δ (2*ηH) (ρ₀/16)
      ((εstar-2*ηH)/2) lam ∧
    ∃βout ξ ζ:ℝ,0<βout ∧ βout=βH/8 ∧ 0<ξ ∧ 0<ζ ∧ ξ≤h/16 ∧ ζ≤h/16 ∧
      h/2≤(2*h-ζparent)-ξ-ζ ∧
    (∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
        OrdinaryVortexGeneralRootGeometryAtScale m k ρ₀ (βH/4) (c*(1-δ)^((m+1)-1))
          (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*ηH+(εstar-2*ηH)/2)
          ((εstar-2*ηH)/2) η βout ξ ζ p eps γ) ∧
    ∀(ε χhost χcut:ℝ),0<ε→ε<1→0<χhost→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
        βP ηP row ηH βH c B εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)) :=by
  obtain ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,hevents⟩:=
    ordinary_general_deep_reference_capacity_hierarchy_quantitative m d hm hd α ρ₀ pstar ηP hα hα1 hθ1 hρ₀ hp hp1 hηP
  refine ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,?_⟩
  intro ηcap hηcap
  obtain ⟨ηH,ζparent,rate,lam,hηH,hηHcap,hηHstar,hζparent,hrate,hlam,hζcap,N₀,hN₀,hscale,hroot,
    βout,ξ,ζ,hβout,hβeq,hξ,hζ,hξcap,hζoutcap,hcut,hgeometry⟩:=
    ordinary_general_deep_packing_before_balance_geometry m k hm (by omega) α εstar hεstar ρ₀ βH c B pstar δ h ηcap (h/16) (h/16)
      hρ₀ hβH hc hB hp hδ hδ1 hh hηcap (by positivity) (by linarith) (by positivity) (by linarith)
  refine ⟨ηH,ζparent,rate,lam,hηH,hηHcap,hηHstar,hζparent,hrate,hlam,hζcap,N₀,hN₀,hscale,hroot,
    βout,ξ,ζ,hβout,hβeq,hξ,hζ,hξcap,hζoutcap,hcut,hgeometry,?_⟩
  intro ε χhost χcut hε hε1 hχhost hχcut
  exact hevents ηH ε χhost χcut hηH hε hε1 hχhost hχcut
end Oberwolfach
