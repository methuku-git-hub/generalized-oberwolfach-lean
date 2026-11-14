module

public import Oberwolfach.OrdinaryDeepEarlyEventCertificateLoadStaticAt
public import Oberwolfach.OrdinaryDeepEarlyEventCertificateLoadStatic
public import Oberwolfach.OrdinaryActualCertificateGeometryStaticAt
public import Oberwolfach.OrdinaryActualCertificateSameHubStatic
public import Oberwolfach.OrdinaryActualCertificateChooseScaleStatic

@[expose] public section
/-! Instantiate one parent certificate with the deep event's hub weights,
choose the vortex scale, then choose the common event and certificate load
before the placement spacing and edit cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_event_certificate_from_geometry_static
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (α βfreq ρ₀ αcut c C a ε₀ ρ θdeep:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1)
    (hα:0<α) (hc:0<c) (hC:0<C) (ha:0<a) (hε₀:0<ε₀)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeLoad mWheel Kdeep α ρ₀ (ρ₀*(βfreq/200)/2) αcut c C a ε₀ ρ θdeep)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear href δlimit ηProfile bParent BParent εparent gap geomCap:ℝ)
    (hgeometry:OrdinaryActualCertificateGeometryStaticAt mWheel Kdeep kcert hm α βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      ρ₀ (ρ₀*(βfreq/200)/2) href δlimit a ρ θdeep (ρ₀*(βfreq/200)/2) ηProfile bParent BParent εparent gap geomCap)
    (root εmax εearly capInner capξ capWeight parentRate pcap:ℝ)
    (hroot:0<root) (hmax:0<εmax) (hearly:0<εearly) (hinner:0<capInner)
    (hcapξ:0<capξ) (hcapWeight:0<capWeight) (hparentRate:0<parentRate) (hpcap:0<pcap):
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
      OrdinaryDeepEarlyEventCertificateLoadStaticAt mWheel Kdeep kcert hm α ρ₀ pstar αcut c C a ε₀ ρ θdeep
        ε ηhub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
        pstar href ηProfile bParent BParent εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γ κ ζhub ζlocal δend lam βe βh θmatch parentRate pcap :=by
  intro pstar
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,βout,ξreserve,ζout,edit,
    hδcut,hδcut1,hδlimit,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hBoundary,hInitial,hNumeric,
    hβout,hβoutEq,hξreserve,hζout,hedit,hξcap,hζcap,
    γ,eParent,hParent,κ,hγ,he,hh,hγe,heB,hhB,heI,hhI,hκ,hκ1,hκρ,hpstar,hpstar1,
    ηhub,ζhub,aEnd,ηend,ζlocal,δend,hη,hζ,haEnd,haEnd1,hηend,hζlocal,hδend,hAfterHub⟩:=
    ordinary_actual_certificate_same_hub_static mWheel Kdeep kcert hm α βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      βfreq ρ₀ pstar href δlimit a ρ θdeep ηProfile bParent BParent εparent gap geomCap c C
      hβfreq hβ1 hρ₀ hρ1 hc hC hgeometry
  obtain ⟨εcap,hεcap,hmax',hearly',hinner',hηcap,haCap,hρCap,
    cMatch,eCleanup,hCleanup,lam,ε,βe,βh,θmatch,hcMatch,heCleanup,hhCleanup,hcBound,hβeEq,hβhEq,hβe,hβh,
    hlam,hlamRoot,hlam1,hlamρ,hlamE,hlamH,hrow,hlevel,hε,hεcap',hεvortex',hε1,hεξ,hεξρ,hεroot,hθEq,hθ,hAfterScale⟩:=
    ordinary_actual_certificate_choose_scale_static mWheel Kdeep kcert hm α βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      ρ₀ pstar href a ρ θdeep pstar ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ c (4*C/pstar^(3*mWheel+1)) pstar κ ηhub ζhub aEnd ηend ζlocal δend hAfterHub
      root eParent hParent εmax εearly capInner hroot he hh hγe heB hhB heI hhI hmax hearly hinner hη ha hρ₀
  have hChosen:OrdinaryDeepEarlyEventCertificateLoadStaticAt mWheel Kdeep kcert hm α ρ₀ pstar αcut c C a ε₀ ρ θdeep
      ε ηhub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      pstar href ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ κ ζhub ζlocal δend lam βe βh θmatch parentRate pcap:=
    ordinary_deep_early_event_certificate_load_static mWheel Kdeep kcert hm α ρ₀ pstar αcut c C a ε₀ ρ θdeep hdeep
      ε ηhub eParent hParent capξ capWeight hε hε1 (hεcap'.trans haCap) (hεcap'.trans hρCap)
      hρ₀ hα hε₀ hη hcapξ hcapWeight ha hc hC hpstar he hh
      βparent ωcert bRoot BRoot hpack δparent εstar cLinear pstar href ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ κ ζhub ζlocal δend lam βe βh θmatch parentRate pcap hparentRate hpcap hAfterScale
  exact ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,βout,ξreserve,ζout,edit,
    hδcut,hδcut1,hδlimit,hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hBoundary,hInitial,hNumeric,
    hβout,hβoutEq,hξreserve,hζout,hedit,hξcap,hζcap,
    γ,eParent,hParent,κ,hγ,he,hh,hγe,heB,hhB,heI,hhI,hκ,hκ1,hκρ,hpstar,hpstar1,
    ηhub,ζhub,aEnd,ηend,ζlocal,δend,hη,hζ,haEnd,haEnd1,hηend,hζlocal,hδend,
    εcap,hεcap,hmax',hearly',hinner',hηcap,haCap,hρCap,
    cMatch,eCleanup,hCleanup,lam,ε,βe,βh,θmatch,hcMatch,heCleanup,hhCleanup,hcBound,hβeEq,hβhEq,hβe,hβh,
    hlam,hlamRoot,hlam1,hlamρ,hlamE,hlamH,hrow,hlevel,hε,hεcap',hεvortex',hε1,hεξ,hεξρ,hεroot,hθEq,hθ,hChosen⟩
end Oberwolfach
