module

public import Oberwolfach.OrdinaryPreSampleGeometryBeforeAbsorberSize
public import Oberwolfach.OrdinaryActualCertificateLocalGeometryPayload
public import Oberwolfach.OrdinaryInitialFineCoverThresholdPayload
public import Oberwolfach.OrdinaryVortexGeometryCostBalanceThresholdPayload
public import Oberwolfach.OrdinaryDeepParentAfterFailurePayload
public import Oberwolfach.OrdinaryThreeStepBalanceThresholdPayload
public import Oberwolfach.OrdinaryLookbackVortexThresholdPayload

@[expose] public section
/-! After the original failure allowances have been fixed, select a single
vortex error and size for an arbitrary compatible certificate payload, the
three-step balance event, and the matching-correction-parent event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_presample_initial_fine_before_absorber_size
    (L rstar d m k dMin Kdeep kParent:ℕ) (hd:2≤d) (hm:3≤rstar-1)
    (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (ε capHub ηBudget δAbs hAbs εabs εv:ℝ)
    (hpre:OrdinaryOriginalPreSampleWithEditRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv)
    (hε:0<ε) (hεsmall:ε<1/4) (hερ:ε≤ρ₀/16) (habs:ε≤εabs) (hv:ε≤εv)
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
    (lam ξreserve ξroot ηbal ηInitial γgeom edit p βe βh βparent bRoot BRoot εparent gap βout ζout ηpack εout costRate:ℝ)
    (hξroot:0≤ξroot)
    (hmin hrefLocal δcut ζcut εcut ζlimit εsample cBoundary cInitial ηProfile ζcert rateCert δcap ηedit:ℝ)
    (hRcap:εR≤δcap) (hHcap:εH≤δcap) (Nextra:ℕ)
    (hsource:∀β:ℝ,0≤β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∀C:ℝ,0≤C→
      ∃mInitial mBalance mCover mEdit Nedit:ℕ,1≤mInitial ∧ 1≤mBalance ∧ 1≤mCover ∧ 1≤mEdit ∧
      OrdinaryInitialMatchingMarginsAt ρ₀ (α/2) (ρ₀*(βfreq/200)/2) hmin ε ηbal cInitial δedit ηedit β d mEdit Nedit ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ (α/2) (ρ₀*(βfreq/200)/2) hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ (α/2) (ρ₀*(βfreq/200)/2) hmin ηProfile ζcert cBoundary δDeep rateCert d 2 β C mBalance ∧
      OrdinaryActualTraceFineCoverAtLocalBalanceLocalHost (rstar-1) Kdeep 2 ρ₀ hmin hrefLocal δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρdeep θdeep β ηbal d mCover ∧
      ∀εR' εH' pH:ℝ,0≤εR'→εR'≤δcap→0≤εH'→εH'≤δcap→0≤pH→pH≤1→
        OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad (rstar-1) Kdeep d kParent β ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh pH εR' εH'
          βparent bRoot BRoot εparent gap βout ζout ηpack εout)
    (hcost:OrdinarySelectedCostRate ε ρ₀ capHub d costRate)
    (hcoverChoice:∀β:ℝ,0≤β→β≤1/4→∃mInitial:ℕ,1≤mInitial ∧
      OrdinaryInitialFineCoverFromSharedAt (rstar-1) Kdeep d ρ₀ hmin hrefLocal a ρdeep θdeep δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal
        αcut (ρ₀*(βfreq/200)/2) β mInitial):
    let Local:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>Nextra≤Nmin ∧ OrdinaryDeepLocalCertificateThresholdPayload (rstar-1) Kdeep d
      ρ₀ (α/2) (ρ₀*(βfreq/200)/2) hmin hrefLocal δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρdeep θdeep
      ηbal cBoundary cInitial δInitial ηInitial ηProfile ζcert δDeep rateCert 0 δedit ηedit β m₀ Nmin;
    let Payload:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>∃mCert mInitial:ℕ,mCert≤m₀ ∧ mInitial≤m₀ ∧ Local β mCert Nmin ∧
      OrdinaryInitialFineCoverFromSharedAt (rstar-1) Kdeep d ρ₀ hmin hrefLocal a ρdeep θdeep δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal
        αcut (ρ₀*(βfreq/200)/2) β mInitial;
    ∃εTri β:ℝ,0<εTri ∧ 0<β ∧ β≤1/4 ∧ β≤α/8 ∧ β≤εTri ∧ β≤βcap ∧ β≤δInitial ∧ β≤δDeep ∧ β≤δedit ∧
    ∃mv mCert Nmin N:ℕ,
    OrdinaryVortexGeometryCostPayload (rstar-1) Kdeep d kParent ε ρ₀ lam ξreserve ξroot aLoad ηbal ηInitial γgeom edit p βe βh εR εH
      βparent bRoot BRoot εparent gap βout ζout ηpack εout capHub costRate β Payload mCert Nmin ∧ mCert≤mv ∧ Nmin≤N ∧ 2/ε≤(N:ℝ) ∧ (N:ℝ)≤ε*mv/2 ∧
    ∀mAbs:ℕ,OrdinaryOriginalPreSampleWithBundleAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly ε capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
      β Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
      kParent hm βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar χthree :=by
  intro Local Payload
  obtain ⟨hLocal,hgeometry⟩:=ordinary_actual_certificate_local_geometry_payload (rstar-1) Kdeep d kParent
    ρ₀ (α/2) (ρ₀*(βfreq/200)/2) hmin hrefLocal δcut ζcut εcut ζlimit εsample ε ξroot aLoad a ρdeep θdeep
    ηbal cBoundary cInitial δInitial ηInitial ηProfile ζcert δDeep rateCert δedit ηedit βcap δcap
    lam ξreserve γgeom edit p βe βh εR εH βparent bRoot BRoot εparent gap βout ζout ηpack εout
    hεR.le hRcap hεH.le hHcap Nextra hsource
  have hPayload:=ordinary_initial_fine_cover_threshold_payload (rstar-1) Kdeep d
    ρ₀ hmin hrefLocal a ρdeep θdeep δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut (ρ₀*(βfreq/200)/2)
    βcap δInitial δDeep δedit hcoverChoice Local hLocal
  exact ordinary_presample_geometry_before_absorber_size L rstar d m k dMin Kdeep kParent hd hm βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hρ1 hα hθhost βPlace lamPlace ζPlace εearly ε capHub ηBudget δAbs hAbs εabs εv hpre
    hε hεsmall hερ habs hv q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
    hζ hχpair hχlist hχbal hχbd hχnbr hχpairR hχpath hχlocal hχglobal hχhub hχcol
    αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep capξ
    hεR hεH hβchoose hdeep βP ηP row ηH βH cParent Bparent χhost δref href χref hpstar hparent
    βcap δInitial δDeep δedit χthree hβcap hδInitial hδDeep hδedit hχthree
    lam ξreserve ξroot ηbal ηInitial γgeom edit p βe βh βparent bRoot BRoot εparent gap βout ζout ηpack εout costRate
    hξroot hgeometry hcost Payload hPayload
end Oberwolfach
