module

public import Oberwolfach.OrdinaryDeepEarlyEventChoosePlacementStatic
public import Oberwolfach.OrdinaryEarlyPlacementExposeFixedEdit

@[expose] public section
/-! The selected deep certificate load, original placement and correction
choices fix the edit rate before any later failure allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_load_expose_fixed_edit
    (mWheel Kdeep kcert:ℕ) (hm:3≤mWheel)
    (αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (ε ηHub eParent hParent capξ capWeight:ℝ)
    (βparent ωcert bRoot BRoot hpack δparent εstar cLinear hmin href ηProfile bParent BParent εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap:ℝ)
    (hchoice:OrdinaryDeepEarlyEventCertificateLoadStaticAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap)
    (L rstar mEarly kEarly dMin:ℕ) (βfreq αOriginal γList capInner θhost capOriginal:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d mEarly kEarly dMin βfreq ρ₀ αOriginal γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly)
    (hcapOriginal:0<capOriginal) (hε:0<ε)
    (βP ηP row ηH βH cParent Bhost δref hrefParent:ℝ) (hp:0<pmin)
    (hparents:∀(d:ℕ) (hd:2≤d),OrdinaryParentEventsAtSpacing mWheel kcert d hm hd αdeep ρ₀ pmin
      βP ηP row ηH βH cParent Bhost δref hrefParent ε hp)
    (αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ωcorr δAbs hAbs εabs εv)
    (hεsample:0<εsample) (hδend:0<δend):
    ∃ξedit:ℝ,0<ξedit ∧ OrdinaryDeepEarlyEventAtFixedEditStatic mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly βP ηP row ηH βH cParent Bhost δref hrefParent hp αcorr pstar ωcorr δAbs hAbs εabs εv ξedit :=by
  have hplacement:=ordinary_deep_early_event_choose_placement_static mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
    ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap hchoice L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
    hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hTail hcapOriginal hε
  exact ordinary_early_placement_expose_fixed_edit mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
    ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
    hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly hplacement
    βP ηP row ηH βH cParent Bhost δref hrefParent hp hparents
    αcorr pstar ωcorr δAbs hAbs εabs εv hε hcorr hεsample hδend
end Oberwolfach
