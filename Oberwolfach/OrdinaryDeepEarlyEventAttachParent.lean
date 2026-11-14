module

public import Oberwolfach.OrdinaryDeepEarlyEventCertificateParentPlacementAt
public import Oberwolfach.OrdinaryDeepEarlyEventCertificatePlacementAt
public import Oberwolfach.OrdinaryActualCertificatePlacementAttachParent

@[expose] public section
/-! Choose the matching spacing using the tolerance from the same local
certificate and keep the earlier common-event and cost choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_early_event_attach_parent
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (ε ηHub eParent hParent capξ capWeight:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap:ℝ)
    (L rstar mEarly kEarly dMin:ℕ) (βfreq αOriginal γList capInner θhost capOriginal:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hchoice:OrdinaryDeepEarlyEventCertificatePlacementAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly)
    (βP ηP row ηH βH cParent Bhost δref hrefParent:ℝ) (hp:0<pmin)
    (hparents:∀(d:ℕ) (hd:2≤d),OrdinaryParentEventsAtSpacing mWheel kcert d hm hd αdeep ρ₀ pmin
      βP ηP row ηH βH cParent Bhost δref hrefParent ε hp):
    OrdinaryDeepEarlyEventCertificateParentPlacementAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent Bhost δref hrefParent hp :=by
  obtain ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB,hβchoose,
    t,eEvent,hEvent,cap,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,hcost,hcostall,
    rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδDeepα,hrate,hratecap,hload,hselect⟩:=hchoice
  have hplacement:=ordinary_actual_certificate_placement_attach_parent mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
    δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend eParent hParent lamCert ε βe βh θmatch rateParent ζ δDeep rate pcap
    L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
    hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hload
    βP ηP row ηH βH cParent Bhost δref hrefParent hp hparents
  exact ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB,hβchoose,
    t,eEvent,hEvent,cap,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,hcost,hcostall,
    rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδDeepα,hrate,hratecap,hplacement,hselect⟩
end Oberwolfach
