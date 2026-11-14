module

public import Oberwolfach.OrdinaryDeepParentAndEarlyEventStaticAt
public import Oberwolfach.OrdinaryDeepEventCertificateFromGeometryStatic

@[expose] public section
/-! Select the common deep event from the same parent weights, sharp
reference scale and local certificate, before the placement spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_parent_choose_early_event_static
    (m loadK:ℕ) (hm:3≤m) (α ρ₀ βfreq ηP:ℝ)
    (hα:0<α) (hρ:0<ρ₀) (hρ1:ρ₀≤1) (hβ:0<βfreq) (hβ1:βfreq≤1)
    (aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit cHub CHub ε₀ εmax εearly capInner capξ capWeight pcap:ℝ)
    (ha:0<aDeep) (hcHub:0<cHub) (hCHub:0<CHub) (hε₀:0<ε₀) (hmax:0<εmax) (hearly:0<εearly)
    (hinner:0<capInner) (hcapξ:0<capξ) (hcapWeight:0<capWeight) (hpcap:0<pcap)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeLoad m loadK α ρ₀ (ρ₀*(βfreq/200)/2) αcut cHub CHub aDeep ε₀ ρdeep θdeep)
    (hparent:OrdinaryParentReferenceDeepJointQuarterAt m loadK hm α ρ₀ (ρ₀*(βfreq/200)/2) ηP (by positivity)
      aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit):
    OrdinaryDeepParentAndEarlyEventStaticAt m loadK hm α ρ₀ βfreq ηP (by positivity)
      aDeep ρdeep θdeep ηProfile αcut ηcap gapcap ζlimit cHub CHub ε₀ εmax εearly capInner capξ capWeight pcap :=by
  obtain ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,
    εCert,cCert,hεCert,hcCert,hcert,ηH,gap,ζcap,geomGap,hη,hηbound,hgap,hgapbound,hζ,hζh,hζbound,hcompat,hgeom,hgeomEq,
    hrefCut,δlimit,geomCap,hhrefCut,hhrefBound,hδlimit,hδlimitBound,hgeomCap,hgeomCapBound,hgeometry,
    ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζparentcap,N₀,hN₀,hscale,hroot,hmono,hevents⟩:=hparent
  have hEvent:=ordinary_deep_event_certificate_from_geometry_static m loadK k hm α βfreq ρ₀ αcut cHub CHub aDeep ε₀ ρdeep θdeep
    hβ hβ1 hρ hρ1 hα hcHub hCHub ha hε₀ hdeep
    (βH/4) (ρ₀/16) (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*(ρ₀*(βfreq/200)/2)^(2*(m+1)-1))) (h/2) (δ/2) εCert cCert
    hrefCut δlimit ηProfile (c*(1-δ)^((m+1)-1)) (B/((ρ₀/16)*(ρ₀*(βfreq/200)/2)^(2*(m+1)-1))) (2*ηH+gap) geomGap geomCap hgeometry
    lamroot εmax εearly capInner capξ capWeight rateParent pcap hlam hmax hearly hinner hcapξ hcapWeight hrate hpcap
  exact ⟨δ,h,βP,row,k,βH,c,B,εstar,cLinear,hδ,hδ1,hh,hβP,hrow,hk,hβH,hc,hB,hεstar,hcLinear,hrule,
    εCert,cCert,hεCert,hcCert,hcert,ηH,gap,ζcap,geomGap,hη,hηbound,hgap,hgapbound,hζ,hζh,hζbound,hcompat,hgeom,hgeomEq,
    hrefCut,δlimit,geomCap,hhrefCut,hhrefBound,hδlimit,hδlimitBound,hgeomCap,hgeomCapBound,hgeometry,
    ζparent,rateParent,lamroot,hζparent,hrate,hlam,hζparentcap,N₀,hN₀,hscale,hroot,hmono,hEvent,hevents⟩
end Oberwolfach
