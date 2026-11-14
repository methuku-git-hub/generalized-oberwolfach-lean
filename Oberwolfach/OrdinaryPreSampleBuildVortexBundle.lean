module

public import Oberwolfach.OrdinaryOriginalPreSampleWithBundleAt

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

theorem ordinary_presample_build_vortex_bundle
    (L rstar d m k dMin:ℕ) (hdExt:2≤d) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (εvortex capHub ηBudget δAbs hAbs εabs εv:ℝ)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (hpre:OrdinaryOriginalPreSampleWithThresholdsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol)
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
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom⟩:=hpre
  have hsmin:smin=βfreq/200:=hSpacing.2.2.2.2.2.1
  subst smin
  let Nhost:=max 2 (max Nsel (max Ncorr (max Ngeom mv)))
  have h2:2≤Nhost:=by dsimp [Nhost]; omega
  have hselN:Nsel≤Nhost:=by dsimp [Nhost]; omega
  have hcorrN:Ncorr≤Nhost:=by dsimp [Nhost]; omega
  have hgeomN:Ngeom≤Nhost:=by dsimp [Nhost]; omega
  have hmvN:mv≤Nhost:=by dsimp [Nhost]; omega
  refine ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,βfreq/200,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    ξedit,ξAbs,hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom,
    Nhost,h2,hselN,hcorrN,hgeomN,hmvN,?_⟩
  intro n qCount D hn hq F hF habundance hρlo hρhi hthreshold P hreg hdegree
  exact ordinary_original_deep_parent_vortex_balance_bundle n qCount D rstar m k d K mv mAbs aAbs bAbs q₀ Nsel Ncorr Nc Ng Nh Ncol Ngeom hd
    βfreq ρ₀ α θ θhost lamMatch aRow γrow ζSel lamSel ζSel τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent
    εvortex εabs εv βv ξAbs χlocal χglobal χhub χcol BO hsel hgeom hlocal (by omega) (by omega) (by omega) (by omega) hq hmv hρ₀ hε
    F hF habundance hρlo hρhi hthreshold P hreg hdegree hθhost hα hβv hβv1
    Kdeep v₀ αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
    hdeep hr hβfreq hdeepSize kParent Mhost Mcut hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref
    hpstar hselector hcuts hε1 hερ hβα hβε hM hMcut χthree mBalance hmBalance hBalanceAt mVortex hmVortex (by omega) hVortex
end Oberwolfach
