module

public import Oberwolfach.OrdinaryActualCertificateLoadWithParentPlacementAt

@[expose] public section
/-! The certificate's load is selected under the very deep-cover cap that
was fixed before the common event and the certificate rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_certificate_placement_attach_parent
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γ bHub BHub p₀ κ ηhub ζhub ζlocal δend:ℝ)
    (eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap:ℝ)
    (L rstar mEarly kEarly dMin:ℕ) (βfreq αOriginal γList capInner θhost capOriginal:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hαOriginal:0<αOriginal)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hload:OrdinaryActualCertificateLoadWithPlacementAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly)
    (βP ηP row ηH βH cParent BParent δref hrefParent:ℝ) (hp:0<pmin)
    (hparents:∀(d:ℕ) (hd:2≤d),OrdinaryParentEventsAtSpacing mWheel k d hm hd α ρ₀ pmin
      βP ηP row ηH βH cParent BParent δref hrefParent ε hp):
    OrdinaryActualCertificateLoadWithParentPlacementAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch rateParent ζ δDeep rate pcap
      L rstar mEarly kEarly dMin βfreq αOriginal γList capInner θhost capOriginal
      hr hβfreq hβ1 hρ₀ hαOriginal βPlace lamPlace ζPlace εearly
      βP ηP row ηH βH cParent BParent δref hrefParent hp :=by
  obtain ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,
    hellEq,hell,hkcap,hpbound,hpcap',hp,hpp,hp1,hpθ,hsqrt,hεsup,hεsupcap,hfinish,hfinishA,hfinishell,
    hδsample,hload,hload1,hloadfinish,hν,hcap,hνfinish,hcapfinish,
    Nfinish,hschedule,τ,ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,
    n₀,εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,δInitial,δedit,ηedit,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadA,haLoadγ,haLoadEdit,hξeq,hξ,hξε,hξγ,hξsq,
    hellRate,hcoverRate,hηeq,hη₀,hηbal,hηbal₀,hηbalγ,hηInitial,hηInitialBal,hβcap,hβcap1,hβcapγ,
    hδcap,hδcapγ,hδInitial,hδInitialα,hδInitialη,hδedit,hδeditα,hδeditη,hηedit,ηBudget,capChosen,hBudget,hBudgetη,hsmall,hChosen,hOriginal,hCap,dSelected,hdSelected,hplacement,hremain⟩:=
    hload
  exact ⟨ellCap,kcap,pbound,p,εsup,finishCap,δsample,loadCap,ν,cap,
    hellEq,hell,hkcap,hpbound,hpcap',hp,hpp,hp1,hpθ,hsqrt,hεsup,hεsupcap,hfinish,hfinishA,hfinishell,
    hδsample,hload,hload1,hloadfinish,hν,hcap,hνfinish,hcapfinish,
    Nfinish,hschedule,τ,ηpack,hτeq,hτ,hτcap,hτ1,hηpack,hlinear,
    n₀,εout,γgeom,aLoad,ξroot,η₀,ηbal,ηInitial,βcap,δcap,δInitial,δedit,ηedit,
    hεout,hεout1,hγgeom,haLoad,haLoad1,haLoadCap,haLoadA,haLoadγ,haLoadEdit,hξeq,hξ,hξε,hξγ,hξsq,
    hellRate,hcoverRate,hηeq,hη₀,hηbal,hηbal₀,hηbalγ,hηInitial,hηInitialBal,hβcap,hβcap1,hβcapγ,
    hδcap,hδcapγ,hδInitial,hδInitialα,hδInitialη,hδedit,hδeditα,hδeditη,hηedit,
    ηBudget,capChosen,hBudget,hBudgetη,hsmall,hChosen,hOriginal,hCap,dSelected,hdSelected,hplacement,hparents dSelected hdSelected,hremain⟩
end Oberwolfach
