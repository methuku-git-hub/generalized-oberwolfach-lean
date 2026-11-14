module

public import Oberwolfach.OrdinaryDeepEarlyEventAtFixedEditStatic
public import Oberwolfach.OrdinaryActualCertificateLoadFixedEditSize

@[expose] public section
/-! Retain the one pre-failure certificate size and conflict budget with
the original fixed edit rate and common parent/deep-event parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

def OrdinaryDeepEarlyFixedEditSizeStatic
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
    (αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ) (ξedit:ℝ) (Nextra:ℕ):Prop :=
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
      OrdinaryActualCertificateLoadAtFixedEditSize mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
        ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend eParent hParent lamCert ε βe βh θmatch rateParent ζ δDeep rate pcap
        L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
        βP ηP row ηH βH cParent Bhost δref hrefParent hp cap αcorr pstar ωcorr δAbs hAbs εabs εv ξedit Nextra ∧
      ∀(aLoad εR εH:ℝ),0<aLoad→aLoad≤a→0<εR→0<εH→
      ∀χinner χdeep χone χtwo χcut:ℝ,0<χinner→0<χdeep→0<χone→0<χtwo→0<χcut→
        OrdinaryDeepRowsCutsAfterParameters mWheel Kdeep αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
          aLoad ε ξdeep b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap



theorem ordinary_deep_early_fixed_edit_size_static
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
    (αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ) (ξedit:ℝ) (Nextra:ℕ) (hε:0<ε)
    (h:OrdinaryDeepEarlyEventAtFixedEditStatic mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent Bhost δref hrefParent hp αcorr pstar ωcorr δAbs hAbs εabs εv ξedit):
    OrdinaryDeepEarlyFixedEditSizeStatic mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent Bhost δref hrefParent hp αcorr pstar ωcorr δAbs hAbs εabs εv ξedit Nextra :=by
  obtain ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hK,hB,hKone,hKtwo,hBweight,hβchoose,
    t,eEvent,hEvent,cap,costRate,ht,he,hh,hcap,heParent,hhParent,hcost,hcostRate,
    rateParent,ζ,δDeep,rate,hrateParent,hrateEnd,hrateCap,hζ,hζlimit,hζrate,hζcap,hδDeep,hδDeepα,hrate,hrateCost,hload,hrows⟩:=h
  have hSized:=ordinary_actual_certificate_load_fixed_edit_size mWheel Kdeep kcert hm αdeep βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    ρ₀ hmin href a ρ θdeep pmin ηProfile bParent BParent εparent gap
    δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert c (4*C/pmin^(3*mWheel+1)) pmin κ ηHub ζhub ζlocalCert δend
    eParent hParent lamCert ε βe βh θmatch rateParent ζ δDeep rate pcap
    L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
    hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
    βP ηP row ηH βH cParent Bhost δref hrefParent hp cap αcorr pstar ωcorr δAbs hAbs εabs εv ξedit Nextra hε hload
  exact ⟨ξdeep,b,Kdom,Bweight,hξ,hξcap,hb,hbc,hbcap,hK,hB,hKone,hKtwo,hBweight,hβchoose,
    t,eEvent,hEvent,cap,costRate,ht,he,hh,hcap,heParent,hhParent,hcost,hcostRate,
    rateParent,ζ,δDeep,rate,hrateParent,hrateEnd,hrateCap,hζ,hζlimit,hζrate,hζcap,hδDeep,hδDeepα,hrate,hrateCost,hSized,hrows⟩
end Oberwolfach
