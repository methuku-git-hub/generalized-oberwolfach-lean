module

public import Oberwolfach.OrdinaryTriangleSharpHostGeometrySelectorWithCutoff
public import Oberwolfach.OrdinaryTriangleReferenceSubmargin

@[expose] public section
/-! Choose the sharp triangle host hierarchy inside the original surplus,
while retaining an arbitrary earlier length cutoff. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_original_margin_sharp_host_geometry_with_cutoff
    (θ α₀ ρ₀ pstar:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1) (hα₀:0<α₀)
    (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1):
    ∃α:ℝ,0<α ∧ α≤α₀ ∧ ∀Nmin:ℕ, (
    ∃δ href βP:ℝ,0<δ ∧ δ<1/8 ∧ 0<href ∧ 0<βP ∧
    (∀(η χ Lconf:ℝ),0<η→η<1→0<χ→0≤Lconf→∀d:ℕ,∀hd:2≤d,∃M:ℕ,1≤M ∧
      OrdinaryReferenceCutsDomainSelector d M hd (α/2) pstar (ρ₀/16) (2*δ) href η χ Lconf) ∧
    ∀(d:ℕ) (hd:2≤d) (ηP:ℝ),0<ηP→
    ∃(k:ℕ) (βH cParent Bparent:ℝ),5≤k ∧ Nmin≤k ∧ 0<βH ∧ 0<cParent ∧ 0<Bparent ∧
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
        (2*ηH+gap) (εstar-(2*ηH+gap)) βout ξ ζ edit p η eps γ ) :=by
  obtain ⟨α,hα,hα₀',hα1,hθmargin⟩:=ordinary_triangle_reference_submargin θ α₀ hθhalf hθcycle hθ1 hα₀
  refine ⟨α,hα,hα₀',?_⟩
  intro Nmin
  exact ordinary_triangle_sharp_host_geometry_selector_with_cutoff Nmin α ρ₀ pstar hα hα1 hρ₀ hpstar hpstar1 hθmargin
end Oberwolfach
