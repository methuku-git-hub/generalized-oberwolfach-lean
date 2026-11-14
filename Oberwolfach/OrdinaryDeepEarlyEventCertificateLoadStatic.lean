module

public import Oberwolfach.OrdinaryDeepCapCostBeforeSpacing
public import Oberwolfach.OrdinaryDeepWeightChoicesBeforeLoad
public import Oberwolfach.OrdinaryDeepSpacingErrorBeforeLateCap
public import Oberwolfach.OrdinaryActualCertificateChooseRatesStatic
public import Oberwolfach.OrdinaryActualCertificateChooseLoadStatic

@[expose] public section
/-! The common event cap, certificate rates and certificate load can all be
selected before the matching spacing and edit cap, with one shared set of
hub and cleanup parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_early_event_certificate_load_static
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsEarlyBeforeLoad mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep)
    (ε ηHub eParent hParent capξ capWeight:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hεa:ε≤a) (hερ:ε≤ρ₀/16)
    (hρ₀:0<ρ₀) (hα:0<αdeep) (hε₀:0<ε₀) (hηHub:0<ηHub)
    (hcapξ:0<capξ) (hcapWeight:0<capWeight) (ha:0<a) (hc:0<c) (hC:0<C) (hpmin:0<pmin)
    (he:0<eParent) (hh:0<hParent)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap:ℝ) (hparentRate:0<parentRate) (hpcap:0<pcap)
    (hcert:OrdinaryActualCertificateAfterScaleStaticAt mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend eParent hParent lamCert ε βe βh θmatch):
    ∃ξdeep b Kdom Bweight:ℝ,
      0<ξdeep ∧ ξdeep≤capξ ∧ 0<b ∧ b≤c ∧ b≤capWeight ∧ 0<Kdom ∧ 0<Bweight ∧
      2/ε≤Kdom ∧ 1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom ∧
      (4*C/pmin^(3*mWheel+1))*Kdom^mWheel≤Bweight ∧
      (∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤αdeep/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξdeep+2*β<ηHub) ∧
    ∃t eEvent hEvent cap costRate:ℝ,
      0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ eEvent≤eParent ∧ hEvent≤hParent ∧
      0<costRate ∧ (∀d:ℕ,OrdinarySelectedCostRate ε ρ₀ cap d costRate) ∧
    ∃rateParent ζ δDeep rate:ℝ,
      0<rateParent ∧ rateParent≤δend*ε/8 ∧ rateParent≤parentRate ∧
      0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ ζ≤cap ∧ 0<δDeep ∧ δDeep≤αdeep ∧ 0<rate ∧ rate≤costRate ∧
      OrdinaryActualCertificateChosenLoadStaticAt mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
        ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend eParent hParent lamCert ε βe βh θmatch rateParent ζ δDeep rate pcap ∧
      ∀(aLoad εR εH:ℝ),0<aLoad→aLoad≤a→0<εR→0<εH→
      ∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap :=by
  obtain ⟨ξdeep,hξ,hξcap,hβchoose⟩:=ordinary_deep_spacing_error_before_late_cap αdeep ε₀ capξ ηHub hα hε₀ hcapξ hηHub
  obtain ⟨b,Kdom,Bweight,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB⟩:=
    ordinary_deep_weight_choices_before_load mWheel a c capWeight ε ρ₀ pmin C ha hc hcapWeight hε hρ₀ hpmin hC
  obtain ⟨t,eEvent,hEvent,cap,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,hcost,hcostall,hselect⟩:=
    ordinary_deep_cap_cost_before_spacing mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep hdeep
      ε ξdeep b Bweight ηHub Kdom eParent hParent hε hε1 hεa hερ hρ₀ hξ hK hKdom hbc hB he hh
  obtain ⟨rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδDeepα,hrate,hratecap,hremain⟩:=
    ordinary_actual_certificate_choose_rates_static mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend eParent hParent lamCert ε βe βh θmatch
      hcert cap costRate parentRate hcap hcost hparentRate
  have hload:=ordinary_actual_certificate_choose_load_static mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
    δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend eParent hParent lamCert ε βe βh θmatch rateParent ζ δDeep rate pcap
    ha hpcap hremain
  exact ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hKpos,hBpos,hK,hKdom,hB,hβchoose,
    t,eEvent,hEvent,cap,costRate,ht,hevent,hhevent,hcap,hebound,hhbound,hcost,hcostall,
    rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδDeepα,hrate,hratecap,hload,hselect⟩
end Oberwolfach
