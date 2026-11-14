module

public import Oberwolfach.OrdinaryTriangleSharpFreshCertificateFamily
public import Oberwolfach.OrdinaryTriangleParentFineSharpRootScaleChoiceAnchored
public import Oberwolfach.OrdinaryTriangleReferenceGeometrySlackChoice
public import Oberwolfach.OrdinaryTriangleFixedDomainSelectorChoice
public import Oberwolfach.OrdinaryNondeeperTriangleToleranceChoice
public import Oberwolfach.OrdinaryReferenceCutsDomainSelectorChoice
public import Oberwolfach.OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale

@[expose] public section
/-! Select the triangle host, sharp root reference and static geometry before
choosing the vortex scale and its size-dependent fresh-factor parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_sharp_host_geometry_selector
    (α ρ₀ pstar:ℝ) (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1)
    (hθ1:max (1/2) (cycleThreshold 3)+α/4≤1):
    ∃δ href βP:ℝ,0<δ ∧ δ<1/8 ∧ 0<href ∧ 0<βP ∧
    (∀(η χ Lconf:ℝ),0<η→η<1→0<χ→0≤Lconf→∀d:ℕ,∀hd:2≤d,∃M:ℕ,1≤M ∧
      OrdinaryReferenceCutsDomainSelector d M hd (α/2) pstar (ρ₀/16) (2*δ) href η χ Lconf) ∧
    ∀(d:ℕ) (hd:2≤d) (ηP:ℝ),0<ηP→
    ∃(k:ℕ) (βH cParent Bparent:ℝ),5≤k ∧ 0<βH ∧ 0<cParent ∧ 0<Bparent ∧
    (∀ηH η χhost χcut:ℝ,0<ηH→0<η→η<1→0<χhost→0<χcut→
      ∃εTri:ℝ,0<εTri ∧ ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) (α/2) pstar
        (ρ₀/16) βP ηP ηH βH cParent Bparent εTri η χhost (2*(3*d)) hpstar ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) pstar (ρ₀/16) (2*δ) href η χcut (2*(3*d))) ∧
    let ω:=ρ₀/16;let βout:=βH/8;let hpack:=href/4;
    let bRoot:=cParent*(1-2*δ)^2;let BRoot:=Bparent/(ω*pstar^(2*3-1));
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
      OrdinaryTriangleSharpFreshCertificateFamily (α/2) k ω βout bRoot BRoot hpack δ εstar cLinear ∧
    ∀ηHcap gapcap ζcap:ℝ,0<ηHcap→0<gapcap→0<ζcap→ζcap≤href→
    ∃ηH gap:ℝ,0<ηH ∧ ηH≤ηHcap ∧ 0<gap ∧ gap≤gapcap ∧ 2*ηH+gap<εstar ∧
    ∃ζRoot rateRoot lamRoot:ℝ,0<ζRoot ∧ 0<rateRoot ∧ 0<lamRoot ∧ ζRoot≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryTriangleEditScaleAt βH ηH Bparent ω pstar (βH/2) (2*ηH) ζRoot rateRoot N₀ ∧
      OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad 2 k 0 (by omega) (α/2) (βH/2) cParent BRoot
        (2*href-ζRoot) (2*δ) (2*ηH) ω gap lamRoot ∧
    ∃ξ ζ edit:ℝ,0<ξ ∧ 0<ζ ∧ 0<edit ∧ ξ≤href/4 ∧ ζ≤href/4 ∧ ξ+ζ≤href/2 ∧
      hpack≤(2*href-ζRoot)-ξ-ζ ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ (βH/4) bRoot BRoot
        (2*ηH+gap) (εstar-(2*ηH+gap)) βout ξ ζ edit p η eps γ :=by
  have hαhalf:0<α/2:=by positivity
  have hαhalf1:α/2≤1/2:=by linarith
  obtain ⟨δfull,href,hδfull,hδfull1,hhref,hcuts0⟩:=ordinary_reference_cuts_domain_selector_choice
    (α/2) pstar (ρ₀/16) hαhalf hαhalf1 hpstar hpstar1 (by positivity)
  let δ:ℝ:=δfull/2
  have hδ:0<δ:=by dsimp [δ];linarith
  have hδ1:δ<1/8:=by dsimp [δ];linarith
  have hδeq:2*δ=δfull:=by dsimp [δ];ring
  have hcuts:∀(η χ Lconf:ℝ),0<η→η<1→0<χ→0≤Lconf→∀d:ℕ,∀hd:2≤d,∃M:ℕ,1≤M ∧
      OrdinaryReferenceCutsDomainSelector d M hd (α/2) pstar (ρ₀/16) (2*δ) href η χ Lconf :=by
    simpa only [hδeq] using hcuts0
  obtain ⟨βP,hβP,hβmax,hβhub,hgeo⟩:=ordinary_nondeeper_triangle_tolerance_choice (α/2) pstar (ρ₀/16)
    hαhalf hpstar (by positivity)
  obtain ⟨Nroot,hcert⟩:=ordinary_triangle_sharp_fresh_certificate_family_choice (α/2) hαhalf
  refine ⟨δ,href,βP,hδ,hδ1,hhref,hβP,hcuts,?_⟩
  intro d hd ηP hηP
  obtain ⟨k,βH,cParent,Bparent,hk,hkN,hβH,hc,hB,hhost⟩:=ordinary_triangle_fixed_domain_selector_choice
    Nroot d hd (max (1/2) (cycleThreshold 3)) (α/2) pstar (ρ₀/16) βP ηP (2*(3*d))
    (le_max_right _ _) hαhalf (by linarith) (by linarith) hpstar hpstar1 (by positivity)
    hβP hβmax hβhub hηP (by positivity)
  refine ⟨k,βH,cParent,Bparent,hk,hβH,hc,hB,?_,?_⟩
  · intro ηH η χhost χcut hηH hη hη1 hχhost hχcut
    obtain ⟨εTri,hεTri,Mhost,hMhost,hselect⟩:=hhost ηH η χhost hηH hη hη1 hχhost
    obtain ⟨Mcut,hMcut,hcut⟩:=hcuts η χcut (2*(3*d)) hη hη1 hχcut (by positivity) d hd
    exact ⟨εTri,hεTri,Mhost,Mcut,hMhost,hMcut,hselect,hcut⟩
  · intro ω βout hpack bRoot BRoot
    have hbase:0<1-2*δ:=by linarith
    have hbRoot:0<bRoot:=by dsimp [bRoot];positivity
    have hBRoot:0<BRoot:=by dsimp [BRoot,ω];positivity
    obtain ⟨εstar,cLinear,hεstar,hcLinear,hcert⟩:=hcert k hkN ω βout bRoot BRoot hpack δ
      (by dsimp [ω];positivity) (by dsimp [βout];positivity) hbRoot hBRoot (by dsimp [hpack];positivity) hδ (by linarith)
    refine ⟨εstar,cLinear,hεstar,hcLinear,hcert,?_⟩
    intro ηHcap gapcap ζcap hηHcap hgapcap hζcap hζhref
    obtain ⟨ηH,gap,hηH,hηHcap',hgap,hgapcap',hfit⟩:=
      ordinary_triangle_reference_geometry_slack_choice εstar ηHcap gapcap hεstar hηHcap hgapcap
    obtain ⟨ζRoot,rateRoot,lamRoot,hζRoot,hrateRoot,hlamRoot,hζcap',N₀,hN₀,hscale,hroot⟩:=
      ordinary_triangle_parent_fine_sharp_root_scale_choice_anchored k (by omega) (α/2) βH ηH cParent Bparent ω pstar
        (2*δ) href gap ζcap hβH hηH hc.le hB.le (by dsimp [ω];positivity) hpstar
        (by positivity) (by linarith) hhref hgap hζcap hζhref
    obtain ⟨βout',ξ,ζ,edit,hβout',hβeq,hξ,hζ,hedit,hξcap,hζcap'',hgeometry⟩:=
      ordinary_vortex_buffered_root_static_geometry_separate_at_scale_choice 3 k 2 (by omega) ρ₀ (βH/4) bRoot BRoot
        (2*ηH+gap) (εstar-(2*ηH+gap)) (href/4) (by omega) hρ₀ (by positivity) hbRoot hBRoot.le
        (by linarith) (by positivity)
    have hβeq':βout'=βout:=by dsimp [βout] at *;linarith
    have hsum:ξ+ζ≤href/2:=by linarith
    have hpackbound:hpack≤(2*href-ζRoot)-ξ-ζ:=by dsimp [hpack];linarith
    refine ⟨ηH,gap,hηH,hηHcap',hgap,hgapcap',hfit,ζRoot,rateRoot,lamRoot,hζRoot,hrateRoot,hlamRoot,hζcap',N₀,hN₀,hscale,hroot,ξ,ζ,edit,hξ,hζ,hedit,hξcap,hζcap'',hsum,hpackbound,?_⟩
    intro pcap hpcap
    obtain ⟨p,hp,hp1,hpCap,hgeometry⟩:=hgeometry pcap hpcap
    refine ⟨p,hp,hp1,hpCap,?_⟩
    intro η hη
    obtain ⟨eps,γ,heps,heps1,hγ,hgeometry⟩:=hgeometry η hη
    refine ⟨eps,γ,heps,heps1,hγ,?_⟩
    rw [hβeq'] at hgeometry
    exact hgeometry
end Oberwolfach
