module

public import Oberwolfach.OrdinaryPreSampleBuildVortexBundle
public import Oberwolfach.OrdinaryPreSampleChooseCommonThresholds

@[expose] public section
/-! The selected matching and correction thresholds determine one ambient
size above which the actual lookback, parent and same-sample balance bundle
is available for every original factor family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_presample_choose_and_build_vortex_bundle
    (L rstar d m k dMin:ℕ) (hdExt:2≤d) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (εvortex capHub ηBudget δAbs hAbs εabs εv:ℝ)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (hpre:OrdinaryOriginalPreSampleWithEditRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv)
    (hρ1:ρ₀≤1) (habs:εvortex≤εabs) (hv:εvortex≤εv)
    (hζ:0<ζ) (hχpair:0<χpair) (hχlist:0<χlist) (hχbal:0<χbal) (hχbd:0<χbd)
    (hχnbr:0<χnbr) (hχpairR:0<χpairR) (hχpath:0<χpath) (hχlocal:0<χlocal)
    (hχglobal:0<χglobal) (hχhub:0<χhub) (hχcol:0<χcol)
    (hε:0<εvortex) (hε1:εvortex≤1) (hερ:εvortex≤ρ₀/16) (hmv:0<mv)
    (βv:ℝ) (hβv:0≤βv) (hβv1:βv≤1/4) (hβα:βv≤α/8)
    (Kdeep v₀:ℕ) (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep:ℝ)
    (hdeep:OrdinaryDeepRowsCutsAfterSpacing (rstar-1) Kdeep d hdExt v₀ βv
      (α/2) ρ₀ (ρ₀*(βfreq/200)/2) αcut c C a ε₀ ρdeep θdeep aLoad εvortex ξdeep bDeep Bweight ηHub Kdom
      χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep) (hdeepSize:v₀≤mv)
    (kParent Mhost Mcut:ℕ) (hmParent:3≤rstar-1)
    (βP ηP row ηH βH cParent Bparent εTri χhost δref href χref:ℝ) (hpstar:0<ρ₀*(βfreq/200)/2)
    (hselector:OrdinaryGeneralFixedDomainSelector (rstar-1) kParent d Mhost hmParent hdExt
      (max (1/2) (cycleThreshold ((rstar-1)+1))) (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/16)
      βP ηP row ηH βH cParent Bparent εTri εvortex χhost (2*(3*d)) hpstar)
    (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hdExt (α/2) (ρ₀*(βfreq/200)/2)
      (ρ₀/16) δref href εvortex χref (2*(3*d))) (hβε:βv≤εTri)
    (hM:(Mhost:ℝ)≤εvortex*mv/2) (hMcut:(Mcut:ℝ)≤εvortex*mv/2)
    (χthree:ℝ) (mBalance mVortex:ℕ) (hmBalance:mBalance≤mv) (hmVortex:mVortex≤mv)
    (hBalanceAt:OrdinaryThreeStepBalanceProductAt d hdExt εR εH βv εvortex ρ₀ χthree mBalance)
    (hVortex:OrdinaryLookbackVortexAt βv εvortex ρ₀ d mVortex):
    OrdinaryOriginalPreSampleWithBundleAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
      βv Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar χthree :=by
  have hthreshold:=ordinary_presample_choose_common_thresholds L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hρ1 hα hθhost βPlace lamPlace ζPlace εearly
    εvortex capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv hpre hε habs hv
    mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
    hζ hχpair hχlist hχbal hχbd hχnbr hχpairR hχpath hχlocal hχglobal hχhub hχcol
  exact ordinary_presample_build_vortex_bundle L rstar d m k dMin hdExt βfreq ρ₀ α γList capInner capEdit θhost
    hr hβfreq hβ1 hρ₀ hα hθhost βPlace lamPlace ζPlace εearly εvortex capHub ηBudget δAbs hAbs εabs εv
    mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol hthreshold
    hε hε1 hερ hmv βv hβv hβv1 hβα Kdeep v₀ αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom
    χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep hdeep hdeepSize
    kParent Mhost Mcut hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar
    hselector hcuts hβε hM hMcut χthree mBalance mVortex hmBalance hmVortex hBalanceAt hVortex
end Oberwolfach
