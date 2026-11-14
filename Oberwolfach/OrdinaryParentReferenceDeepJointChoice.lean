module

public import Oberwolfach.OrdinaryParentJointReferenceChoices
public import Oberwolfach.OrdinaryParentReferenceChosenCompatible
public import Oberwolfach.OrdinaryParentDeepCertificateGeometry
public import Oberwolfach.OrdinaryReferenceCertificateGapChoices
public import Oberwolfach.OrdinaryGeneralFineParentRootScaleChoice
public import Oberwolfach.OrdinaryGeneralEditScaleRateMonotone

@[expose] public section
/-! Select the all-level parent tests and the general-load sharp root from
one reference parameter family, retaining its allowable later edit rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_parent_reference_deep_joint_choice
    (m loadK d:ℕ) (hm:3≤m) (hd:2≤d) (α ρ₀ pstar ηP:ℝ)
    (hp:0<pstar) (hρ₀:0<ρ₀) (aDeep ρdeep θdeep ηProfile αcut:ℝ)
    (haDeep:0<aDeep) (hρdeep:0<ρdeep) (hθdeep:0<θdeep) (hprofile:0<ηProfile) (hαcut:0<αcut)
    (ηcap gapcap ζlimit:ℝ) (hηcap:0<ηcap) (hgapcap:0<gapcap) (hζlimit:0<ζlimit)
    (hchoices:OrdinaryParentReferenceCompatibleChoices m loadK d hm hd α ρ₀ pstar ηP hp):
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
    ∀(ε χhost χcut:ℝ),0<ε→ε<1→0<χhost→0<χcut→
    ∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/4 ∧ βmax≤εTri ∧
    ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryGeneralFixedDomainSelector m k d Mhost hm hd (max (1/2) (cycleThreshold (m+1))) α pstar (ρ₀/16)
        βP ηP row ηH βH c B εTri ε χhost (2*(3*d)) hp ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd α pstar (ρ₀/16) δ h ε χcut (2*(3*d)) :=by
  obtain ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,
    εCert,cCert,hεCert,hcCert,hcert,ηH,gap,ζcap,geomGap,hη,hηbound,hgap,hgapbound,hζ,hζh,hζbound,hcompat,hgeom,hgeomEq,
    ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζparentcap,N₀,hN₀,hscale,hroot,hmono,hevents⟩:=
    ordinary_parent_reference_chosen_compatible m loadK d hm hd α ρ₀ pstar ηP hp ηcap gapcap ζlimit hηcap hgapcap hζlimit hchoices
  obtain ⟨hrefCut,δlimit,geomCap,hhrefCut,hhrefBound,hδlimit,hδlimitBound,hgeomCap,hgeomCapBound,hgeometry⟩:=
    ordinary_parent_deep_certificate_geometry m loadK k hm α ρ₀ pstar βH c B δ h εCert cCert hρ₀ hp hβH hc hB hδ hδ1 hh
      ηH gap geomGap aDeep ρdeep θdeep ηProfile αcut hη hgap hgeom hgeomEq haDeep hρdeep hθdeep hprofile hαcut hcert
  exact ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,
    εCert,cCert,hεCert,hcCert,hcert,ηH,gap,ζcap,geomGap,hη,hηbound,hgap,hgapbound,hζ,hζh,hζbound,hcompat,hgeom,hgeomEq,
    hrefCut,δlimit,geomCap,hhrefCut,hhrefBound,hδlimit,hδlimitBound,hgeomCap,hgeomCapBound,hgeometry,
    ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζparentcap,N₀,hN₀,hscale,hroot,hmono,hevents⟩
end Oberwolfach
