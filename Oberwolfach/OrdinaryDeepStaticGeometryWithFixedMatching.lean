module

public import Oberwolfach.OrdinaryDeepEventCertificateFromGeometryStaticAt
public import Oberwolfach.OrdinaryDeepStaticEventWithFixedMatching

@[expose] public section
/-! Preserve the selected deep wheel geometry and attach matching and
correction rates to its exact event cap before failure choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach

def OrdinaryDeepEventCertificateFromGeometryStaticWithFixedMatchingAt
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (α βfreq ρ₀ αcut c C a ε₀ ρ θdeep:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear href δlimit ηProfile bParent BParent εparent gap geomCap:ℝ)
    (root εmax εearly capInner capξ capWeight parentRate pcap:ℝ)
    (L rstar m k dMin:ℕ) (hr:3≤rstar)
    (αOriginal γList θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace αcorr pcorr ωcorr δAbs hAbs εabs εv:ℝ):Prop :=
    let pstar:=ρ₀*(βfreq/200)/2;
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧ 0<cInitial ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ pstar href a ρ θdeep δcut ζcut εcut ζlimit εsample εvortex ∧
      0<βout ∧ βout=βparent/2 ∧ 0<ξreserve ∧ 0<ζout ∧ 0<edit ∧ ξreserve≤geomCap ∧ ζout≤geomCap ∧
    ∃γ eParent hParent κ:ℝ,0<γ ∧ 0<eParent ∧ 0<hParent ∧ γ≤eParent ∧
      eParent≤cBoundary ∧ hParent≤cBoundary ∧ eParent≤cInitial ∧ hParent≤cInitial ∧
      0<κ ∧ κ≤1 ∧ κ≤ρ₀/8 ∧ 0<pstar ∧ pstar≤1 ∧
    ∃ηhub ζhub aEnd ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<aEnd ∧ aEnd≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∃εcap:ℝ,0<εcap ∧ εcap≤εmax ∧ εcap≤εearly ∧ εcap≤capInner ∧ εcap≤ηhub ∧ εcap≤a ∧ εcap≤ρ₀/16 ∧
    ∃cMatch eCleanup hCleanup lam ε βe βh θmatch:ℝ,
      0<cMatch ∧ eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζhub*γ*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2 ∧
      βe=eCleanup*ε ∧ βh=hCleanup*ε ∧ 0<βe ∧ 0<βh ∧
      0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*(((Kdeep:ℝ)+1)*lam)≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε≤εvortex ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
      θmatch=cMatch*ε ∧ 0<θmatch ∧
      OrdinaryDeepEarlyEventCertificateLoadStaticWithFixedMatchingAt mWheel Kdeep kcert hm α ρ₀ pstar αcut c C a ε₀ ρ θdeep
        ε ηhub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
        pstar href ηProfile bParent BParent εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γ κ ζhub ζlocal δend lam βe βh θmatch parentRate pcap
        L rstar m k dMin hr βfreq ρ₀ αOriginal γList capInner θhost
        hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly αcorr pcorr ωcorr δAbs hAbs εabs εv

theorem ordinary_deep_static_geometry_with_fixed_matching
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (α βfreq ρ₀ αcut c C a ε₀ ρ θdeep:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear href δlimit ηProfile bParent BParent εparent gap geomCap:ℝ)
    (root εmax εearly capInner capξ capWeight parentRate pcap:ℝ)
    (L rstar m k dMin:ℕ) (hr:3≤rstar)
    (αOriginal γList θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace αcorr pcorr ωcorr δAbs hAbs εabs εv:ℝ)
    (hselected:OrdinaryDeepEventCertificateFromGeometryStaticAt mWheel Kdeep kcert hm α βfreq ρ₀ αcut c C a ε₀ ρ θdeep
      βparent ωcert bRoot BRoot hpack δparent εstar cLinear href δlimit ηProfile bParent BParent εparent gap geomCap
      root εmax εearly capInner capξ capWeight parentRate pcap)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ αOriginal γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly)
    (hρ1:ρ₀≤1) (hθhost:1/2≤θhost)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pcorr ωcorr δAbs hAbs εabs εv)
    (hmMatch:7≤m) (hInnerAbs:capInner≤εabs) (hInnerV:capInner≤εv)
    (hEarly:OrdinaryPlacementEarlyRateData (αOriginal/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin):
    OrdinaryDeepEventCertificateFromGeometryStaticWithFixedMatchingAt mWheel Kdeep kcert hm α βfreq ρ₀ αcut c C a ε₀ ρ θdeep
      βparent ωcert bRoot BRoot hpack δparent εstar cLinear href δlimit ηProfile bParent BParent εparent gap geomCap
      root εmax εearly capInner capξ capWeight parentRate pcap
      L rstar m k dMin hr αOriginal γList θhost hβfreq hβ1 hρ₀ hαOriginal
      βPlace lamPlace ζPlace αcorr pcorr ωcorr δAbs hAbs εabs εv :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,βout,ξreserve,ζout,edit,
    hδcut,hδquarter,hδlimit,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvquarter,hBoundary,hInitial,hNumeric,
    hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,
    γ,eParent,hParent,κ,hγ,heParent,hhParent,hγe,heBoundary,hhBoundary,heInitial,hhInitial,hκ,hκ1,hκρ,hpstar,hpstar1,
    ηhub,ζhub,aEnd,ηend,ζlocal,δend,hηhub,hζhub,haEnd,haEnd1,hηend,hζlocal,hδend,
    εcap,hεcap,hεmax,hεearly,hεinner,hεhub,hεa,hερ,
    cMatch,eCleanup,hCleanup,lam,ε,βe,βh,θmatch,hcMatch,heCleanup,hhCleanup,hcMatchcap,
    hβeeq,hβheq,hβe,hβh,hlam,hlamroot,hlamquarter,hlamρ,hlamβe,hlamβh,hrow,hlevel,
    hε,hεcap',hεvortex',hεquarter,hεξ,hεξρ,hεroot,hθeq,hθ,hEvent⟩:=hselected
  have hEventMatch:=ordinary_deep_static_event_with_fixed_matching mWheel Kdeep kcert hm α ρ₀ (ρ₀*(βfreq/200)/2) αcut c C a ε₀ ρ θdeep
    ε ηhub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear (ρ₀*(βfreq/200)/2) href ηProfile bParent BParent εparent gap
    δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γ κ ζhub ζlocal δend lam βe βh θmatch parentRate pcap
    L rstar m k dMin hr βfreq ρ₀ αOriginal γList capInner θhost hβfreq hβ1 hρ₀ hαOriginal
    βPlace lamPlace ζPlace εearly αcorr pcorr ωcorr δAbs hAbs εabs εv hEvent hTail hρ1 hθhost hε hcorr
    hmMatch (hεcap'.trans hεearly) (hεcap'.trans (hεinner.trans hInnerAbs)) (hεcap'.trans (hεinner.trans hInnerV)) hEarly
  exact ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,βout,ξreserve,ζout,edit,
    hδcut,hδquarter,hδlimit,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvquarter,hBoundary,hInitial,hNumeric,
    hβout,hβeq,hξreserve,hζout,hedit,hξcap,hζcap,
    γ,eParent,hParent,κ,hγ,heParent,hhParent,hγe,heBoundary,hhBoundary,heInitial,hhInitial,hκ,hκ1,hκρ,hpstar,hpstar1,
    ηhub,ζhub,aEnd,ηend,ζlocal,δend,hηhub,hζhub,haEnd,haEnd1,hηend,hζlocal,hδend,
    εcap,hεcap,hεmax,hεearly,hεinner,hεhub,hεa,hερ,
    cMatch,eCleanup,hCleanup,lam,ε,βe,βh,θmatch,hcMatch,heCleanup,hhCleanup,hcMatchcap,
    hβeeq,hβheq,hβe,hβh,hlam,hlamroot,hlamquarter,hlamρ,hlamβe,hlamβh,hrow,hlevel,
    hε,hεcap',hεvortex',hεquarter,hεξ,hεξρ,hεroot,hθeq,hθ,hEventMatch⟩
end Oberwolfach
