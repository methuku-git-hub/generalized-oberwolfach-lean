module

public import Oberwolfach.OrdinaryDeepParentPlacementFixedEditStatic
public import Oberwolfach.OrdinaryDeepEarlyEventAtFixedEditStatic

@[expose] public section
/-! Select one positive edit rate before any failure allowance, retaining
the original parent, placement, correction and certificate choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_parent_placement_expose_edit
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
    (hchoice:OrdinaryDeepEarlyEventCertificateParentPlacementStaticAt mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent Bhost δref hrefParent hp)
    (αcorr pstar ωcorr δAbs hAbs εabs εv:ℝ) (hε:0<ε)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ωcorr δAbs hAbs εabs εv)
    (hεsample:0<εsample) (hδend:0<δend):
    ∃ξedit:ℝ,0<ξedit ∧ OrdinaryDeepEarlyEventAtFixedEditStatic mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
      ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
      hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent Bhost δref hrefParent hp αcorr pstar ωcorr δAbs hAbs εabs εv ξedit :=by
  have hfixed:=ordinary_deep_parent_placement_fixed_edit_static mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
    ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
    L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
    hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
    βP ηP row ηH βH cParent Bhost δref hrefParent hp hchoice αcorr pstar ωcorr δAbs hAbs εabs εv hε hcorr hεsample hδend
  exact ordinary_deep_early_event_at_fixed_edit_static mWheel Kdeep kcert hm αdeep ρ₀ pmin αcut c C a ε₀ ρ θdeep
    ε ηHub eParent hParent capξ capWeight βparent ωcert bRoot BRoot hpack δparent εstar cLinear
    hmin href ηProfile bParent BParent εparent gap δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
    γcert κ ζhub ζlocalCert δend lamCert βe βh θmatch parentRate pcap
    L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
    hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
    βP ηP row ηH βH cParent Bhost δref hrefParent hp αcorr pstar ωcorr δAbs hAbs εabs εv hfixed
end Oberwolfach
