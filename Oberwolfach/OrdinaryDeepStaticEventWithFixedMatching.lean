module

public import Oberwolfach.OrdinaryDeepEarlyEventCertificateLoadStaticAt
public import Oberwolfach.OrdinaryFixedEventRatesAndThresholds

@[expose] public section
/-! Attach fixed matching and correction rates to the very cap selected by
 the deep wheel certificate, before all subsequent failure parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach

def OrdinaryDeepEarlyEventCertificateLoadStaticWithFixedMatchingAt
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (ε ηHub eParent hParent capξ capWeight:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap:ℝ)
    (L rstar m k dMin:ℕ) (hr:3≤rstar)
    (βfreq ρMatch αOriginal γList capInner θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρMatch:0<ρMatch) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly αcorr pcorr ωcorr δAbs hAbs εabs εv:ℝ):Prop :=
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
      (∀capEdit ηBudget:ℝ,0<capEdit→0<ηBudget→
        ∃d:ℕ,∃hd:2≤d,∃ξedit ξAbs:ℝ,ξedit≤cap ∧ ξAbs≤cap ∧
        OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρMatch αOriginal γList capInner capEdit θhost
          hr hβfreq hβ1 hρMatch hαOriginal βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pcorr ωcorr δAbs hAbs εabs εv ξedit ξAbs ∧
        ∀(βv:ℝ) (mv:ℕ) (ζfail χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ),
          0<ζfail→0<χpair→0<χlist→0<χbal→0<χbd→0<χnbr→0<χpairR→0<χpath→
          0<χlocal→0<χglobal→0<χhub→0<χcol→
          OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L rstar d m k dMin βfreq ρMatch αOriginal γList capInner capEdit θhost
            hr hβfreq hβ1 hρMatch hαOriginal βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pcorr ωcorr δAbs hAbs εabs εv
            mv (2*mv) 10 ζfail χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv) ∧
      ∀(aLoad εR εH:ℝ),0<aLoad→aLoad≤a→0<εR→0<εH→
      ∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap

theorem ordinary_deep_static_event_with_fixed_matching
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (ε ηHub eParent hParent capξ capWeight:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap:ℝ)
    (L rstar m k dMin:ℕ) (hr:3≤rstar)
    (βfreq ρMatch αOriginal γList capInner θhost:ℝ)
    (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρMatch:0<ρMatch) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly αcorr pcorr ωcorr δAbs hAbs εabs εv:ℝ)
    (hselected:OrdinaryDeepEarlyEventCertificateLoadStaticAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρMatch αOriginal γList capInner capEdit θhost
        hr hβfreq hβ1 hρMatch hαOriginal βPlace lamPlace ζPlace εearly)
    (hρ1:ρMatch≤1) (hθhost:1/2≤θhost) (hε:0<ε)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pcorr ωcorr δAbs hAbs εabs εv)
    (hmMatch:7≤m) (hεearly:ε≤εearly) (habs:ε≤εabs) (hv:ε≤εv)
    (hEarly:OrdinaryPlacementEarlyRateData (αOriginal/2) ρMatch (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin):
    OrdinaryDeepEarlyEventCertificateLoadStaticWithFixedMatchingAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar m k dMin hr βfreq ρMatch αOriginal γList capInner θhost
      hβfreq hβ1 hρMatch hαOriginal βPlace lamPlace ζPlace εearly αcorr pcorr ωcorr δAbs hAbs εabs εv :=by
  obtain ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hK,hB,hK1,hK2,hWeight,hbeta,
    t,eEvent,hEvent,cap,costRate,ht,he,hh,hcap,hebound,hhbound,hcost,hcostAt,
    rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδα,hrate,hratecost,hchosen,hselect⟩:=hselected
  refine ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hK,hB,hK1,hK2,hWeight,hbeta,
    t,eEvent,hEvent,cap,costRate,ht,he,hh,hcap,hebound,hhbound,hcost,hcostAt,
    rateParent,ζ,δDeep,rate,hrp,hrpend,hrpParent,hζ,hζlimit,hζrp,hζcap,hδDeep,hδα,hrate,hratecost,hchosen,?_,hselect⟩
  intro capEdit ηBudget hcapEdit hη
  obtain ⟨d,hd,hpre⟩:=hTail capEdit hcapEdit
  obtain ⟨ξedit,ξAbs,hξeditcap,hξAbscap,hjoint⟩:=
    ordinary_fixed_event_joint_matching_rates L rstar d m k dMin hr hd βfreq ρMatch αOriginal γList capInner capEdit θhost
      hβfreq hβ1 hρMatch hαOriginal βPlace lamPlace ζPlace εearly hpre
      ε cap ηBudget αcorr pcorr ωcorr δAbs hAbs εabs εv hε hcap hη hcorr
  have hthresholds:=ordinary_general_fixed_rates_to_joint_thresholds L rstar d m k dMin hr βfreq ρMatch αOriginal γList capInner capEdit θhost
    hβfreq hβ1 hρMatch hρ1 hαOriginal hθhost βPlace lamPlace ζPlace εearly ε cap ηBudget αcorr pcorr ωcorr δAbs hAbs εabs εv ξedit ξAbs
    hjoint hmMatch hε hεearly habs hv hEarly
  exact ⟨d,hd,ξedit,ξAbs,hξeditcap,hξAbscap,hjoint,hthresholds⟩
end Oberwolfach
