module

public import Oberwolfach.OrdinaryTriangleRootFreeSharpInnerFamilyBeforeSpacing
public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy
public import Oberwolfach.OrdinaryTriangleFixedDomainSelectorBeforeSpacing
public import Oberwolfach.OrdinaryTriangleReferenceSubmargin
public import Oberwolfach.OrdinaryNondeeperTriangleToleranceChoice
public import Oberwolfach.OrdinaryReferenceCutsDomainSelectorChoice
public import Oberwolfach.OrdinaryTriangleParentRootScaleChoiceAnchored
public import Oberwolfach.OrdinaryTriangleBufferedGeometryBeforeSpacing
public import Oberwolfach.OrdinaryTriangleReferenceGeometrySlackChoice

@[expose] public section
/-! Choose the triangle hierarchy at an already fixed positive host margin.
This exposes the margin before selecting the inner-hub weight constants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_sharp_numeric_fixed_margin
    (pmin κe bHub BHub α ρ₀ pstar ηP:ℝ)
    (hpmin:0<pmin) (hpmin1:pmin≤1) (hκe:0<κe) (hbHub:0<bHub) (hBHub:0≤BHub)
    (hα:0<α) (hα1:α≤1) (hmargin:max (1/2) (cycleThreshold 3)+α/4≤1)
    (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1) (hηP:0<ηP):
    ∃δ href βP:ℝ,0<δ ∧ δ<1/8 ∧ 0<href ∧ 0<βP ∧
    ∃k:ℕ,∃βH cParent Bparent:ℝ,5≤k ∧ 0<βH ∧ 0<cParent ∧ 0<Bparent ∧
    (∀(d:ℕ) (hd:2≤d),∀ηH η χhost χcut:ℝ,0<ηH→0<η→η<1→0<χhost→0<χcut→
      ∃εTri:ℝ,0<εTri ∧ ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) (α/2) pstar
        (ρ₀/16) βP ηP ηH βH cParent Bparent εTri η χhost (2*(3*d)) hpstar ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) pstar (ρ₀/16) (2*δ) href η χcut (2*(3*d))) ∧
    ∃εstar cLinear εf ηhub ηend ζfresh εrows:ℝ,0<εstar ∧ 0<cLinear ∧ 0<εf ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζfresh ∧ 0<εrows ∧
    ∃δInner εcount tpot lamInner:ℝ,
      OrdinaryTriangleInnerNumericParameters pmin κe εf ηend εrows δInner εcount tpot lamInner ∧
      OrdinaryTriangleRootFreeSharpInnerAfterChoice (α/2) k (ρ₀/16) (βH/8) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (href/4) δ εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows ∧
    ∀ηHcap gapcap ζcap:ℝ,0<ηHcap→0<gapcap→0<ζcap→ζcap≤href→
    ∃ηH gap:ℝ,0<ηH ∧ ηH≤ηHcap ∧ 0<gap ∧ gap≤gapcap ∧ 2*ηH+gap<εstar ∧
    ∃ζroot rateRoot lamRoot:ℝ,0<ζroot ∧ 0<rateRoot ∧ 0<lamRoot ∧ ζroot≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryTriangleEditScaleAt βH ηH Bparent (ρ₀/16) pstar (βH/2) (2*ηH) ζroot rateRoot N₀ ∧
      OrdinaryUniformRootReferenceAtScale 3 (by omega) k (α/2) (βH/2) cParent (Bparent/((ρ₀/16)*pstar^(2*3-1)))
        (2*href-ζroot) (2*δ) (2*ηH) (ρ₀/16) gap lamRoot ∧
    ∃ξGeo ζGeo edit:ℝ,0<ξGeo ∧ 0<ζGeo ∧ 0<edit ∧ ξGeo≤href/4 ∧ ζGeo≤href/4 ∧ ξGeo+ζGeo≤href/2 ∧
      href/4≤(2*href-ζroot)-ξGeo-ζGeo ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ (βH/4) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (2*ηH+gap) (εstar-(2*ηH+gap))
        (βH/8) ξGeo ζGeo edit p η eps γgeo :=by
  have hαhalf:0<α/2:=by positivity
  have hαhalf1:α/2≤1/2:=by linarith
  obtain ⟨δref,href,hδref,hδref1,hhref,hcuts⟩:=
    ordinary_reference_cuts_domain_selector_choice (α/2) pstar (ρ₀/16) hαhalf hαhalf1 hpstar hpstar1 (by positivity)
  obtain ⟨βP,hβP,hβmax,hβhub,_hbeta⟩:=ordinary_nondeeper_triangle_tolerance_choice (α/2) pstar (ρ₀/16)
    hαhalf hpstar (by positivity)
  obtain ⟨N,hfamily⟩:=ordinary_triangle_root_free_sharp_inner_family_before_spacing (α/2) hαhalf
  obtain ⟨k,βH,cParent,Bparent,hk,hkN,hβH,hc,hB,hselector⟩:=
    ordinary_triangle_fixed_domain_selector_before_spacing N (max (1/2) (cycleThreshold 3)) (α/2) pstar (ρ₀/16) βP ηP
      (le_max_right _ _) hαhalf (by linarith) (by linarith) hpstar hpstar1 (by positivity) hβP hβmax hβhub hηP
  let δ:=δref/2
  let bRoot:=cParent*(1-2*δ)^2
  let BRoot:=Bparent/((ρ₀/16)*pstar^(2*3-1))
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδsmall:δ<1/8:=by dsimp [δ];linarith
  have hbase:0<1-2*δ:=by linarith
  have hbRoot:0<bRoot:=by dsimp [bRoot];positivity
  have hBRoot:0<BRoot:=by dsimp [BRoot];positivity
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hfamily⟩:=hfamily k hkN (ρ₀/16) (βH/8) bRoot BRoot (href/4) δ
      (by positivity) (by positivity) hbRoot hBRoot (by positivity) hδ (by linarith)
  obtain ⟨εf,ηhub,ηend,ζfresh,εrows,hεf,hηhub,hηend,hζfresh,hεrows,hfamily⟩:=
    hfamily κe pmin bHub BHub hκe hpmin hpmin1 hbHub hBHub
  obtain ⟨δInner,εcount,tpot,lamInner,hnum⟩:=
    ordinary_triangle_inner_numeric_hierarchy pmin κe εf ηend εrows hpmin hκe hεf hηend hεrows
  refine ⟨δ,href,βP,hδ,hδsmall,hhref,hβP,k,βH,cParent,Bparent,hk,hβH,hc,hB,?_,
    εstar,cLinear,εf,ηhub,ηend,ζfresh,εrows,hεstar,hcLinear,hεf,hηhub,hηend,hζfresh,hεrows,
    δInner,εcount,tpot,lamInner,hnum,hfamily,?_⟩
  · intro d hd ηH η χhost χcut hηH hη hη1 hχhost hχcut
    obtain ⟨εTri,hεTri,Mhost,hMhost,hhost⟩:=hselector d hd (2*(3*d)) (by positivity) ηH η χhost hηH hη hη1 hχhost
    obtain ⟨Mcut,hMcut,hcut⟩:=hcuts η χcut (2*(3*d)) hη hη1 hχcut (by positivity) d hd
    refine ⟨εTri,hεTri,Mhost,Mcut,hMhost,hMcut,hhost,?_⟩
    convert hcut using 1 <;> congr! 8 <;> dsimp [δ] <;> ring
  · intro ηHcap gapcap ζcap hηHcap hgapcap hζcap hζhref
    obtain ⟨ηH,gap,hηH,hηHcap',hgap,hgapcap',hfit⟩:=
      ordinary_triangle_reference_geometry_slack_choice εstar ηHcap gapcap hεstar hηHcap hgapcap
    obtain ⟨ζroot,rateRoot,lamRoot,hζroot,hrate,hlam,hζcap',N₀,hN₀,hscale,hroot⟩:=
      ordinary_triangle_parent_root_scale_choice_anchored k (by omega) (α/2) βH ηH cParent Bparent (ρ₀/16) pstar
        (2*δ) href gap ζcap hβH hηH hc.le hB.le (by positivity) hpstar (by positivity) (by linarith) hhref hgap hζcap hζhref
    obtain ⟨ξGeo,ζGeo,edit,hξ,hζ,hedit,hξcap,hζcapGeo,hξζ,hpack,hstatic⟩:=
      ordinary_triangle_buffered_geometry_before_spacing k ρ₀ βH cParent Bparent pstar δ href εstar ηH gap
        (by omega) hρ₀ hβH hc hB.le hpstar hδ hδsmall hhref hηH hgap hfit
    exact ⟨ηH,gap,hηH,hηHcap',hgap,hgapcap',hfit,ζroot,rateRoot,lamRoot,hζroot,hrate,hlam,hζcap',
      N₀,hN₀,hscale,hroot,ξGeo,ζGeo,edit,hξ,hζ,hedit,hξcap,hζcapGeo,hξζ,hpack ζroot (hζcap'.trans hζhref),hstatic⟩
end Oberwolfach
