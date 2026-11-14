module

public import Oberwolfach.OrdinaryTriangleOriginalRootFreeCoherentActualSelection

@[expose] public section
/-! Select the reference and vortex/inner numeric data in their required
order, before any host or failure allowance is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_original_vortex_reference_choice
    (pmin κe α c C ρ₀ pstar ηP:ℝ) (hpstar:0<pstar)
    (hroot:OrdinaryTriangleOriginalRootFreeCoherentActualAtMargin pmin κe α c C ρ₀ pstar ηP hpstar)
    (εcap eParent hParent otherβcap:ℝ) (hεcap:0<εcap) (he:0<eParent) (hh:0<hParent) (hother:0<otherβcap):
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
    ∃ξGeo ζGeo edit:ℝ,0<ξGeo ∧ 0<ζGeo ∧ 0<edit ∧ ξGeo≤href/4 ∧ ζGeo≤href/4 ∧ ξGeo+ζGeo≤href/2 ∧
      href/4≤(2*href-ζroot)-ξGeo-ζGeo ∧
    ∃lam ε βe βh θmatch ellCap:ℝ,
      OrdinaryTriangleEarlyVortexData ρ₀ lamRoot ξGeo edit εcap ζfresh
        (min (pmin^4/32) (endpointCountCoefficient pmin κe/4)/4) lam ε βe βh θmatch ellCap ∧
      OrdinaryTriangleEndpointNumericDomainExists (α/2) c C ε ρ₀ pmin ηhub eParent hParent κe ηend εf εrows otherβcap ∧
      OrdinaryTriangleRootFreeRateActualAfterVortex (α/2) k (ρ₀/16) (βH/8) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (href/4) δ εstar cLinear κe pmin c (4*C/pmin^7)
        εf ηhub ηend ζfresh εrows ρ₀ (βH/4) (2*ηH+gap) (εstar-(2*ηH+gap))
        ξGeo ζGeo edit eParent hParent (min (pmin^4/32) (endpointCountCoefficient pmin κe/4)/4) ε βe βh ellCap :=by
  obtain ⟨δ,href,βP,hδ,hδsmall,hhref,hβP,k,βH,cParent,Bparent,hk,hβH,hcParent,hBparent,hselection,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hlinear,hεf,hηhub,hηend,hζfresh,hrows,hrowsGeom,hfamily,hmore⟩:=hroot
  obtain ⟨ηH,gap,hηH,_hηCap,hgap,_hgapCap,hfit,ζroot,rateRoot,lamRoot,hζroot,hrateRoot,hlamRoot,hζcap,
    N₀,hN₀,hscale,hrefRoot,ξGeo,ζGeo,edit,hξ,hζ,hedit,hξcap,hζgeocap,hξζ,hpack,_hstatic,hvortex⟩:=
      hmore 1 1 (href/2) (by norm_num) (by norm_num) (by positivity) (by linarith)
  obtain ⟨lam,ε,βe,βh,θmatch,ellCap,hv,hnum,hrate⟩:=hvortex εcap eParent hParent otherβcap hεcap he hh hother
  exact ⟨δ,href,βP,hδ,hδsmall,hhref,hβP,k,βH,cParent,Bparent,hk,hβH,hcParent,hBparent,hselection,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hlinear,hεf,hηhub,hηend,hζfresh,hrows,hrowsGeom,hfamily,
    ηH,gap,ζroot,rateRoot,lamRoot,hηH,hgap,hfit,hζroot,hζcap,hrateRoot,hlamRoot,N₀,hN₀,hscale,hrefRoot,
    ξGeo,ζGeo,edit,hξ,hζ,hedit,hξcap,hζgeocap,hξζ,hpack,lam,ε,βe,βh,θmatch,ellCap,hv,hnum,hrate⟩
end Oberwolfach
