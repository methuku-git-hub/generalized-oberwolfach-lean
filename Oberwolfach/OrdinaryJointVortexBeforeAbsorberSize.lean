module

public import Oberwolfach.OrdinaryPreSampleFixedVortexBeforeAbsorberSize
public import Oberwolfach.OrdinaryJointVortexBundleSeparateLists

@[expose] public section
/-! Select the common parent, balance and vortex with the exact fixed
matching and correction witnesses before the absorber size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_joint_vortex_before_absorber_size
    (L rstar d m k dMin Kdeep kParent:ℕ) (hd:2≤d) (hm:3≤rstar-1)
    (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (ε capHub ηBudget δAbs hAbs εabs εv ξedit ξAbs:ℝ)
    (hpre:OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv ξedit ξAbs)
    (hε:0<ε) (hεsmall:ε<1/4) (hερ:ε≤ρ₀/16) (habs:ε≤εabs) (hv:ε≤εv)
    (hmMatch:7≤m) (hεearly:ε≤εearly)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin)
    (q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (hζ:0<ζ) (hχpair:0<χpair) (hχlist:0<χlist) (hχbal:0<χbal) (hχbd:0<χbd)
    (hχnbr:0<χnbr) (hχpairR:0<χpairR) (hχpath:0<χpath) (hχlocal:0<χlocal)
    (hχglobal:0<χglobal) (hχhub:0<χhub) (hχcol:0<χcol)
    (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep capξ:ℝ)
    (hεR:0<εR) (hεH:0<εH)
    (hβchoose:∀betaCap:ℝ,0<betaCap→∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤(α/2)/8 ∧ β≤ε₀ ∧ β≤capξ ∧ β≤betaCap ∧ ξdeep+2*β<ηHub)
    (hdeep:OrdinaryDeepRowsCutsAfterParameters (rstar-1) Kdeep (α/2) ρ₀ (ρ₀*(βfreq/200)/2)
      αcut c C a ε₀ ρdeep θdeep aLoad ε ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep)
    (βP ηP row ηH βH cParent Bparent χhost δref href χref:ℝ) (hpstar:0<ρ₀*(βfreq/200)/2)
    (hparent:∃εTri βmax:ℝ,0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤(α/2)/4 ∧ βmax≤εTri ∧
      ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
        OrdinaryGeneralFixedDomainSelector (rstar-1) kParent d Mhost hm hd
          (max (1/2) (cycleThreshold ((rstar-1)+1))) (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16)
          βP ηP row ηH βH cParent Bparent εTri ε χhost (2*(3*d)) hpstar ∧
        OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) (ρ₀*(βfreq/200)/2)
          (ρ₀/16) δref href ε χref (2*(3*d)))
    (βcap δInitial δDeep δedit χthree:ℝ)
    (hβcap:0<βcap) (hδInitial:0<δInitial) (hδDeep:0<δDeep) (hδedit:0<δedit) (hχthree:0<χthree)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤εTri ∧ β≤βcap ∧ β≤δInitial ∧ β≤δDeep ∧ β≤δedit ∧
    ∃mv mCert Nmin N:ℕ,Payload β mCert Nmin ∧ mCert≤mv ∧ Nmin≤N ∧ 2/ε≤(N:ℝ) ∧ (N:ℝ)≤ε*mv/2 ∧
    ∀mAbs:ℕ,OrdinaryOriginalPreSampleJointVortexBundleSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
      β Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
      kParent hm βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar χthree ξedit ξAbs :=by
  let WithBalance:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>
    ∃mCert mBalance:ℕ,mCert≤m₀ ∧ mBalance≤m₀ ∧ Payload β mCert Nmin ∧
      OrdinaryThreeStepBalanceProductAt d hd εR εH β ε ρ₀ χthree mBalance
  have hWithBalance:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,WithBalance β m₀ Nmin:=
    ordinary_three_step_balance_threshold_payload d hd εR εH ε ρ₀ χthree βcap δInitial δDeep δedit
      hεR hεH hε hεsmall hρ₀ hχthree Payload hPayload
  let WithVortex:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>
    ∃mCombined mVortex:ℕ,mCombined≤m₀ ∧ mVortex≤m₀ ∧ WithBalance β mCombined Nmin ∧
      OrdinaryLookbackVortexAt β ε ρ₀ d mVortex
  have hWithVortex:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,WithVortex β m₀ Nmin:=
    ordinary_lookback_vortex_threshold_payload d ε ρ₀ βcap δInitial δDeep δedit hε hεsmall hρ₀ WithBalance hWithBalance
  obtain ⟨εTri,β,hεTri,hβ,hβone,hβα,hβTri,hβcap',hβInitial,hβDeep,hβEdit,v₀,Mhost,Mcut,hv₀,hMhost,hMcut,
    hdeepAfter,hselector,hcuts,m₀,Nmin,hpayload,N,mv,hNmin,hNsize,hmv,hvsize,hm₀,hNterminal,hM,hMcut⟩:=
    ordinary_deep_parent_after_failure_payload (rstar-1) Kdeep kParent d hm hd (α/2) ρ₀ (ρ₀*(βfreq/200)/2)
      αcut c C a ε₀ ρdeep θdeep aLoad ε ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep capξ
      βP ηP row ηH βH cParent Bparent χhost δref href χref βcap δInitial δDeep δedit hpstar
      hβcap hδInitial hδDeep hδedit hε WithVortex hWithVortex hβchoose hdeep hparent
  obtain ⟨mCombined,mVortex,hmCombined,hmVortex,hbalancePayload,hVortex⟩:=hpayload
  obtain ⟨mCert,mBalance,hmCert,hmBalance,hcert,hBalanceAt⟩:=hbalancePayload
  have hβa:β≤α/8:=by linarith
  have hε1:ε≤1:=by linarith

  refine ⟨εTri,β,hεTri,hβ,hβone,hβa,hβTri,hβcap',hβInitial,hβDeep,hβEdit,
    mv,mCert,Nmin,N,hcert,by omega,hNmin,hNsize,hNterminal,?_⟩
  intro mAbs
  have hterminal:=ordinary_original_presample_joint_terminal_separate_lists_at L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv ξedit ξAbs β
    hpre hmMatch hθhost hε hεearly hEarly
  have hthreshold:=ordinary_presample_choose_joint_thresholds_separate_lists L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hρ1 hα hθhost βPlace lamPlace ζPlace εearly ε capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv ξedit ξAbs β
    hterminal hε habs hv mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
    hζ hχpair hχlist hχbal hχbd hχnbr hχpairR hχpath hχlocal hχglobal hχhub hχcol
  exact ordinary_presample_build_joint_vortex_bundle_separate_lists L rstar d m k dMin hd βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hα hθhost βPlace lamPlace ζPlace εearly ε capHub ηBudget δAbs hAbs εabs εv ξedit ξAbs
    mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol β hthreshold
    hε hε1 hερ (by omega) hβ.le hβone hβa Kdeep v₀ αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom
    χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep hdeepAfter hvsize
    kParent Mhost Mcut hm βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar hselector hcuts hβTri hM hMcut
    χthree mBalance mVortex (by omega) (by omega) hBalanceAt hVortex
end Oberwolfach
