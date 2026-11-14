module

public import Oberwolfach.OrdinaryTriangleOriginalRootFreeCoherentSelection
public import Oberwolfach.OrdinaryTriangleRootFreeCoherentEarlyChoicesWithDomain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleOriginalRootFreeCoherentDomainAtMargin
    (pmin κe α c C ρ₀ pstar ηP:ℝ) (hpstar:0<pstar):Prop :=
    ∃δ href βP:ℝ,0<δ ∧ δ<1/8 ∧ 0<href ∧ 0<βP ∧
    ∃k:ℕ,∃βH cParent Bparent:ℝ,5≤k ∧ 0<βH ∧ 0<cParent ∧ 0<Bparent ∧
    (∀(d:ℕ) (hd:2≤d),∀ηH η χhost χcut:ℝ,0<ηH→0<η→η<1→0<χhost→0<χcut→
      ∃εTri:ℝ,0<εTri ∧ ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) (α/2) pstar
        (ρ₀/16) βP ηP ηH βH cParent Bparent εTri η χhost (2*(3*d)) hpstar ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) pstar (ρ₀/16) (2*δ) href η χcut (2*(3*d))) ∧
    ∃εstar cLinear εf ηhub ηend ζfresh εrows:ℝ,
      0<εstar ∧ 0<cLinear ∧ 0<εf ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζfresh ∧ 0<εrows ∧
      εrows≤min (pmin^4/16) (pmin^3/2) ∧
      OrdinaryTriangleRootFreeSharpInnerAfterChoice (α/2) k (ρ₀/16) (βH/8) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (href/4) δ εstar cLinear κe pmin c (4*C/pmin^7)
        εf ηhub ηend ζfresh εrows ∧
    ∀ηHcap gapcap ζcap:ℝ,0<ηHcap→0<gapcap→0<ζcap→ζcap≤href→
    ∃ηH gap:ℝ,0<ηH ∧ ηH≤ηHcap ∧ 0<gap ∧ gap≤gapcap ∧ 2*ηH+gap<εstar ∧
    ∃ζroot rateRoot lamRoot:ℝ,0<ζroot ∧ 0<rateRoot ∧ 0<lamRoot ∧ ζroot≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryTriangleEditScaleAt βH ηH Bparent (ρ₀/16) pstar (βH/2) (2*ηH) ζroot rateRoot N₀ ∧
      OrdinaryUniformRootReferenceAtScale 3 (by omega) k (α/2) (βH/2) cParent (Bparent/((ρ₀/16)*pstar^(2*3-1)))
        (2*href-ζroot) (2*δ) (2*ηH) (ρ₀/16) gap lamRoot ∧
    ∃ξGeo ζGeo edit:ℝ,0<ξGeo ∧ 0<ζGeo ∧ 0<edit ∧ ξGeo≤href/4 ∧ ζGeo≤href/4 ∧ ξGeo+ζGeo≤href/2 ∧
      href/4≤(2*href-ζroot)-ξGeo-ζGeo ∧
    (∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
      ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ (βH/4) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (2*ηH+gap) (εstar-(2*ηH+gap))
        (βH/8) ξGeo ζGeo edit p η eps γgeo) ∧
    let γbase:=min (pmin^4/32) (endpointCountCoefficient pmin κe/4)/4;
    ∀εcap eParent hParent otherβcap:ℝ,0<εcap→0<eParent→0<hParent→0<otherβcap→
    ∃lam ε βe βh θmatch ellCap:ℝ,
      OrdinaryTriangleEarlyVortexData ρ₀ lamRoot ξGeo edit εcap ζfresh γbase lam ε βe βh θmatch ellCap ∧
      OrdinaryTriangleEndpointNumericDomainExists (α/2) c C ε ρ₀ pmin ηhub eParent hParent κe ηend εf εrows otherβcap ∧
      OrdinaryTriangleRootFreeRateAfterVortex (α/2) k (ρ₀/16) (βH/8) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (href/4) δ εstar cLinear κe pmin c (4*C/pmin^7)
        εf ηhub ηend ζfresh εrows ρ₀ (βH/4) (2*ηH+gap) (εstar-(2*ηH+gap))
        ξGeo ζGeo edit eParent hParent γbase ε βe βh ellCap

theorem ordinary_triangle_original_root_free_coherent_of_numeric_with_domain
    (pmin κe α c C ρ₀ pstar ηP:ℝ) (hpstar:0<pstar)
    (hpmin:0<pmin) (hpmin1:pmin≤1) (hκe:0<κe) (hα:0<α) (hc:0<c) (hC:0<C) (hρ:0<ρ₀)
    (hselector:OrdinaryNamedTriangleInnerEndpointSelector (α/2) c C)
    (hnum:OrdinaryTriangleRootFreeNumericBoundedAtMargin pmin κe c (4*C/pmin^7) α ρ₀ pstar ηP hpstar):
    OrdinaryTriangleOriginalRootFreeCoherentDomainAtMargin pmin κe α c C ρ₀ pstar ηP hpstar :=by
  obtain ⟨δ,href,βP,hδ,hδsmall,hhref,hβP,k,βH,cParent,Bparent,hk,hβH,hcParent,hBparent,hselection,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hlinear,hεf,hηhub,hηend,hζfresh,hrows,hrowsGeom,
    δInner,εcount,tInner,lamInner,_hinner,hfamily,hgeometry⟩:=hnum
  refine ⟨δ,href,βP,hδ,hδsmall,hhref,hβP,k,βH,cParent,Bparent,hk,hβH,hcParent,hBparent,hselection,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hlinear,hεf,hηhub,hηend,hζfresh,hrows,hrowsGeom,hfamily,?_⟩
  intro ηHcap gapcap ζcap hηHcap hgapcap hζcap hζhref
  obtain ⟨ηH,gap,hηH,hηHcap',hgap,hgapcap',hfit,ζroot,rateRoot,lamRoot,hζroot,hrateRoot,hlamRoot,hζbound,
    N₀,hN₀,hscale,hroot,ξGeo,ζGeo,edit,hξ,hζ,hedit,hξbound,hζboundGeo,hξζ,hpack,hstatic⟩:=
      hgeometry ηHcap gapcap ζcap hηHcap hgapcap hζcap hζhref
  refine ⟨ηH,gap,hηH,hηHcap',hgap,hgapcap',hfit,ζroot,rateRoot,lamRoot,hζroot,hrateRoot,hlamRoot,hζbound,
    N₀,hN₀,hscale,hroot,ξGeo,ζGeo,edit,hξ,hζ,hedit,hξbound,hζboundGeo,hξζ,hpack,hstatic,?_⟩
  intro γbase εcap eParent hParent otherβcap hεcap he hh hother
  have hγ:0<γbase:=ordinary_triangle_inner_scale_coefficient_pos pmin κe hpmin hκe
  exact ordinary_triangle_root_free_coherent_early_choices_with_domain (α/2) k (ρ₀/16) (βH/8) (cParent*(1-2*δ)^2)
    (Bparent/((ρ₀/16)*pstar^(2*3-1))) (href/4) δ εstar cLinear κe pmin c C εf ηhub ηend ζfresh εrows
    (by positivity) hlinear hζfresh hκe hpmin hpmin1 hc hC hεf hηhub hηend hrows hrowsGeom hfamily hselector
    ρ₀ (βH/4) (2*ηH+gap) (εstar-(2*ηH+gap)) ξGeo ζGeo edit lamRoot εcap eParent hParent γbase otherβcap
    hρ hξ hedit hlamRoot hεcap he hh hγ hother hstatic

theorem ordinary_triangle_original_root_free_coherent_selection_with_domain
    (θ α₀ ρ₀ pstar ηP pmin κe:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1) (hα₀:0<α₀)
    (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1) (hηP:0<ηP)
    (hpmin:0<pmin) (hpmin1:pmin≤1) (hκe:0<κe):
    ∃α c C:ℝ,0<α ∧ α≤α₀ ∧ α≤1 ∧ max (1/2) (cycleThreshold 3)+α/4≤1 ∧
      0<c ∧ 0<C ∧ OrdinaryNamedTriangleInnerEndpointSelector (α/2) c C ∧
      OrdinaryTriangleOriginalRootFreeCoherentDomainAtMargin pmin κe α c C ρ₀ pstar ηP hpstar :=by
  obtain ⟨α,c,C,hα,hαsub,hα1,hmargin,hc,hC,hselector,hnum⟩:=
    ordinary_triangle_original_root_free_bounded_inner_endpoint_hierarchy θ α₀ ρ₀ pstar ηP pmin κe
      hθhalf hθcycle hθ1 hα₀ hρ₀ hpstar hpstar1 hηP hpmin hpmin1 hκe
  have hselector':OrdinaryNamedTriangleInnerEndpointSelector (α/2) c C:=hselector
  exact ⟨α,c,C,hα,hαsub,hα1,hmargin,hc,hC,hselector',
    ordinary_triangle_original_root_free_coherent_of_numeric_with_domain pmin κe α c C ρ₀ pstar ηP hpstar
      hpmin hpmin1 hκe hα hc hC hρ₀ hselector' hnum⟩
end Oberwolfach
