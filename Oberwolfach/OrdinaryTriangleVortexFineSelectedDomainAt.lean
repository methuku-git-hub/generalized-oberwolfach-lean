module

public import Oberwolfach.OrdinaryTriangleVortexFineReferenceSelectionAt
public import Oberwolfach.OrdinaryTriangleInnerSelectedNumericDomain

@[expose] public section
/-! Retain the selected inner numerical domain with the same fine reference
and vortex scale, before the failure allowances and host are chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryTriangleVortexFineSelectedDomainAt
    (pmin κe α c C ρ₀ pstar ηP:ℝ) (hpstar:0<pstar)
    (εcap eParent hParent otherβcap:ℝ):Prop :=
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
    ∃ηH gap ζroot rateRoot lamRoot:ℝ,0<ηH ∧ 0<gap ∧ 2*ηH+gap<εstar ∧
      0<ζroot ∧ ζroot≤href/2 ∧ 0<rateRoot ∧ 0<lamRoot ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryTriangleEditScaleAt βH ηH Bparent (ρ₀/16) pstar (βH/2) (2*ηH) ζroot rateRoot N₀ ∧
      OrdinaryUniformRootReferenceAtScale 3 (by omega) k (α/2) (βH/2) cParent (Bparent/((ρ₀/16)*pstar^(2*3-1)))
        (2*href-ζroot) (2*δ) (2*ηH) (ρ₀/16) gap lamRoot ∧
    ∃lamFine:ℝ,0<lamFine ∧
      OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad 2 k 0 (by omega) (α/2) (βH/2) cParent
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (2*href-ζroot) (2*δ) (2*ηH) (ρ₀/16) gap lamFine ∧
    ∃ξGeo ζGeo edit:ℝ,0<ξGeo ∧ 0<ζGeo ∧ 0<edit ∧ ξGeo≤href/4 ∧ ζGeo≤href/4 ∧ ξGeo+ζGeo≤href/2 ∧
      href/4≤(2*href-ζroot)-ξGeo-ζGeo ∧
    ∃lam ε βe βh θmatch ellCap:ℝ,
      OrdinaryTriangleEarlyVortexData ρ₀ lamRoot ξGeo edit εcap ζfresh
        (min (pmin^4/32) (endpointCountCoefficient pmin κe/4)/4) lam ε βe βh θmatch ellCap ∧ lam≤lamFine ∧
    ∃ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold βcap:ℝ,
      OrdinaryTriangleInnerSelectedNumericDomain (α/2) c C ε ρ₀ pmin ηhub eParent hParent κe ηend εf εrows otherβcap
        ξInner Kdom BInner tHub eEvent hEvent capInner γold κold δInner tpot lamInner bold Bold βcap ∧
      OrdinaryTriangleRootFreeRateActualAfterVortex (α/2) k (ρ₀/16) (βH/8) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (href/4) δ εstar cLinear κe pmin c (4*C/pmin^7)
        εf ηhub ηend ζfresh εrows ρ₀ (βH/4) (2*ηH+gap) (εstar-(2*ηH+gap))
        ξGeo ζGeo edit eParent hParent (min (pmin^4/32) (endpointCountCoefficient pmin κe/4)/4) ε βe βh ellCap


theorem ordinary_triangle_vortex_fine_selected_domain_at
    (pmin κe α c C ρ₀ pstar ηP:ℝ) (hpstar:0<pstar)
    (εcap eParent hParent otherβcap:ℝ)
    (h:OrdinaryTriangleVortexFineReferenceSelectionAt pmin κe α c C ρ₀ pstar ηP hpstar εcap eParent hParent otherβcap):
    OrdinaryTriangleVortexFineSelectedDomainAt pmin κe α c C ρ₀ pstar ηP hpstar εcap eParent hParent otherβcap :=by
  obtain ⟨δ,href,βP,hδ,hδsmall,hhref,hβP,k,βH,cParent,Bparent,hk,hβH,hcParent,hBparent,hselection,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hlinear,hεf,hηhub,hηend,hζfresh,hrows,hrowsGeom,hfamily,
    ηH,gap,ζroot,rateRoot,lamRoot,hηH,hgap,hfit,hζroot,hζcap,hrateRoot,hlamRoot,N₀,hN₀,hscale,hrefRoot,
    lamFine,hlamFine,hfine,ξGeo,ζGeo,edit,hξ,hζ,hedit,hξcap,hζgeocap,hξζ,hpack,lam,ε,βe,βh,θmatch,ellCap,hv,hlamFineBound,hnum,hrate⟩:=h
  obtain ⟨ξInner,Kdom,BInner,tHub,eEvent,hEvent,capInner,γold,κold,δInner,tpot,lamInner,bold,Bold,βcap,hselected⟩:=
    ordinary_triangle_inner_selected_numeric_domain (α/2) c C ε ρ₀ pmin ηhub eParent hParent κe ηend εf εrows otherβcap hnum
  exact ⟨δ,href,βP,hδ,hδsmall,hhref,hβP,k,βH,cParent,Bparent,hk,hβH,hcParent,hBparent,hselection,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hlinear,hεf,hηhub,hηend,hζfresh,hrows,hrowsGeom,hfamily,
    ηH,gap,ζroot,rateRoot,lamRoot,hηH,hgap,hfit,hζroot,hζcap,hrateRoot,hlamRoot,N₀,hN₀,hscale,hrefRoot,
    lamFine,hlamFine,hfine,ξGeo,ζGeo,edit,hξ,hζ,hedit,hξcap,hζgeocap,hξζ,hpack,lam,ε,βe,βh,θmatch,ellCap,hv,hlamFineBound,
    ξInner,Kdom,BInner,tHub,eEvent,hEvent,capInner,γold,κold,δInner,tpot,lamInner,bold,Bold,βcap,hselected,hrate⟩
end Oberwolfach
