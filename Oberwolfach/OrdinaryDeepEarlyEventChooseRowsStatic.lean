module

public import Oberwolfach.OrdinaryDeepEarlyEventCertificateRowsStaticAt
public import Oberwolfach.OrdinaryDeepEarlyEventCertificateRatesStaticAt
public import Oberwolfach.OrdinaryActualCertificateLoadChooseRowsStatic
public import Oberwolfach.OrdinaryActualCertificateLoadWithRatesStaticAt

@[expose] public section
/-! Name the full early-event and certificate-load choice so it can be
carried without expanding its later sample and spacing callbacks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_early_event_choose_rows_static
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (ε ηHub eParent hParent capξ capWeight:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap:ℝ)
    (L rstar mEarly kEarly dMin:ℕ) (βfreq αOriginal γList capInner θhost capOriginal:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (βP ηP row ηH βH cParent Bhost δref hrefParent:ℝ) (hp:0<pmin)
    (αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ)
    (hεsample:0<εsample) (hδend:0<δend)
    (hchoice:OrdinaryDeepEarlyEventCertificateRatesStaticAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent Bhost δref hrefParent hp αcorr pstar ωcorr δAbs hAbs εabs εv):
    OrdinaryDeepEarlyEventCertificateRowsStaticAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent Bhost δref hrefParent hp αcorr pstar ωcorr δAbs hAbs εabs εv :=by
  obtain ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB,hβchoose,
    t,eEvent,hEvent,cap,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,hcost,hcostall,
    rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδDeepα,hrate,hratecap,hload,hselect⟩:=hchoice
  have hrows:=ordinary_actual_certificate_load_choose_rows_static mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
    δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend eParent hParent lamCert ε βe βh θmatch rateParent ζ δDeep rate pcap
    L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
    hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
    βP ηP row ηH βH cParent Bhost δref hrefParent hp cap αcorr pstar ωcorr δAbs hAbs εabs εv hεsample hδend hδDeep hload
  exact ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB,hβchoose,
    t,eEvent,hEvent,cap,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,hcost,hcostall,
    rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδDeepα,hrate,hratecap,hrows,hselect⟩
end Oberwolfach
