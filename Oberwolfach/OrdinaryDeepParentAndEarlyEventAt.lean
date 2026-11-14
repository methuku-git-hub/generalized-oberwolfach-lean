module

public import Oberwolfach.OrdinaryParentReferenceDeepJointBeforeSpacingAt
public import Oberwolfach.OrdinaryDeepEventCertificateFromGeometryAt

@[expose] public section
/-! Parent reference and common event selected together before the matching
spacing and placement edit cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryDeepParentAndEarlyEventAt
    (m loadK:ℕ) (hm:3≤m) (α ρ₀ βfreq ηP:ℝ) (hp:0<ρ₀*(βfreq/200)/2)
    (aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit cHub CHub ε₀ εmax εearly capInner capξ capWeight pcap:ℝ):Prop :=
    let pstar:=ρ₀*(βfreq/200)/2;
    ∃(δ h βP row:ℝ) (k:ℕ) (βH c B εstar cLinear:ℝ),
      0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<βP ∧ 0<row ∧ m+3≤k ∧
      0<βH ∧ 0<c ∧ 0<B ∧ 0<εstar ∧ 0<cLinear ∧
      OrdinaryGeneralDeepSafeCapacityRuleLinear m k hm α (ρ₀/16) (βH/8)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εstar cLinear ∧
      ∃εCert cCert:ℝ,0<εCert ∧ 0<cCert ∧
      OrdinaryActualCertificateReferenceSelectedAt m loadK k hm α (βH/2) (ρ₀/16)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εCert cCert ∧
    ∃ηH gap ζcap geomGap:ℝ,0<ηH ∧ ηH≤ηcap ∧ 0<gap ∧ gap≤gapcap ∧
      0<ζcap ∧ ζcap≤h ∧ ζcap≤ζlimit ∧ 2*ηH+gap<εCert ∧
      0<geomGap ∧ (2*ηH+gap)+geomGap=εCert ∧
    ∃hrefCut δlimit geomCap:ℝ,0<hrefCut ∧ hrefCut≤αcut*pstar/64 ∧
      0<δlimit ∧ δlimit≤min (αcut/32) (pstar/512) ∧ 0<geomCap ∧ 2*geomCap≤h/2 ∧
      OrdinaryActualCertificateGeometryAt m loadK k hm α (βH/2) (ρ₀/16)
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εCert cCert
        ρ₀ pstar hrefCut δlimit aDeep ρdeep θdeep pstar ηProfile
        (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*ηH+gap) geomGap geomCap ∧
    ∃ζparent rateParent lamroot:ℝ,0<ζparent ∧ 0<rateParent ∧ 0<lamroot ∧ ζparent≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryGeneralEditScaleAt (m+1) βH ηH B (ρ₀/16) pstar (βH/2) (2*ηH) ζparent rateParent N₀ ∧
      OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad m k loadK (by omega) α (βH/2) c
        (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*h-ζparent) δ (2*ηH) (ρ₀/16) gap lamroot ∧
      (∀rate:ℝ,rate≤rateParent→OrdinaryGeneralEditScaleAt (m+1) βH ηH B (ρ₀/16) pstar
        (βH/2) (2*ηH) ζparent rate N₀) ∧
      OrdinaryDeepEventCertificateFromGeometryAt m loadK k hm α βfreq ρ₀ αcut cHub CHub aDeep ε₀ ρdeep θdeep
        (βH/2) (ρ₀/16) (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (h/2) (δ/2) εCert cCert
        hrefCut δlimit ηProfile (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*pstar^(2*(m+1)-1))) (2*ηH+gap) geomGap geomCap
        lamroot εmax εearly capInner capξ capWeight rateParent pcap ∧
    ∀(d:ℕ) (hd:2≤d),∀(ε χhost χcut:ℝ),0<ε→ε<1→0<χhost→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
        βP ηP row ηH βH c B εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d))
end Oberwolfach
