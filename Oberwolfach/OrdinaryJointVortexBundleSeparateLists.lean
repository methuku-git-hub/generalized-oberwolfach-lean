module

public import Oberwolfach.OrdinaryPreSampleBuildFixedVortexBundle
public import Oberwolfach.OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt

@[expose] public section
/-! Retain the exact fixed correction and separate-list matching witnesses
while constructing the original parent, balance and vortex bundle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryOriginalPreSampleJointVortexBundleSeparateListsAt
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace ε:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (βv:ℝ) (Kdeep:ℕ) (αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep:ℝ)
    (kParent:ℕ) (hmParent:3≤rstar-1) (βP ηP row ηH βH cParent Bparent εTri χhost δref href χref:ℝ)
    (hpstar:0<ρ₀*(βfreq/200)/2) (χthree ξedit ξAbs:ℝ):Prop :=
    let smin₀:=βfreq/200;let αCap:=5*ρ₀*smin₀^2/128;
    ∃δ θ κ b z matchErr σ κ':ℝ,∃dNeed:ℕ,
      OrdinaryPlacementStage m dNeed αCap lamPlace ζPlace capEdit δ θ κ b z matchErr σ κ' ∧
    ∃βSel lamSel ζSel smin:ℝ,∃K rank:ℕ,
      OrdinaryOriginalSelectorSpacingBounds rstar m dNeed dMin d K rank βfreq θ βSel lamSel ζSel smin ∧
    ∃ζret:ℝ,∃N:ℕ,∃lamMatch aRow γrow:ℝ,∃BO:Fin K → ℝ,
      OrdinaryPlacementAfterSpacing m d N αCap δ θ κ b z matchErr ζret ∧
      OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lamMatch aRow γrow ∧
      (∀i,0<BO i) ∧
      ∃hd:2 ≤ d,OrdinaryOriginalThresholdAfterMatchingRates rstar m k d K hd βfreq ρ₀ α θ θhost
        lamMatch aRow γrow ζSel lamSel ζSel smin BO ∧
      ∃τ tMatch ξMatch bMatch:ℝ,
        OrdinaryOriginalThresholdAfterMatchChoice rstar m k d K hd βfreq ρ₀ α θ θhost
          lamMatch aRow γrow ζSel lamSel ζSel smin τ tMatch ξMatch bMatch BO ∧
        let cBudget:=min (1/1024:ℝ) (min (αCap/4096) (1/2:ℝ)/8);
        OrdinaryEarlyUniformColumnsBeforeAbsorberShape d m
          lamPlace ζPlace b ε cBudget θ z δ aRow γrow (θ/2) bMatch αCap ∧
          0<ξedit ∧ ξedit≤capHub*εvortex/1000 ∧ ξedit≤ηBudget/1000 ∧ ξedit≤σ ∧ ξedit≤ζPlace/8 ∧ ξedit≤bMatch ∧
          OrdinaryEarlyUniformColumnsAtRate d m lamPlace ζPlace b ε cBudget θ z δ aRow γrow (θ/2) bMatch αCap ξedit ∧
          0<ξAbs ∧ ξAbs≤capHub*εvortex/1000 ∧ ξAbs≤ηBudget/1000 ∧ ξAbs≤σ ∧ ξAbs≤hAbs/100 ∧
          (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices rstar d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) ∧
          (∀rate ξroot:ℝ,0≤rate→0≤ξroot→∀mAbs tAbs aAbs bAbs:ℕ,
            OrdinaryOriginalTerminalConditionalPreparationSeparateListsAt rstar m k d K hd βfreq ρ₀ α θhost εvortex βv
              δ θ aRow γrow σ lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs) ∧
        ∃aAbs bAbs:ℕ,∃aEvent:ℝ,0<aEvent ∧ ∃Nsel Ncorr Nc Ng Nh Ncol Ngeom:ℕ,
          1≤Ncorr ∧ 1≤Nc ∧ 1≤Ng ∧ 1≤Nh ∧ 1≤Ncol ∧ 1≤Ngeom ∧
          OrdinaryOriginalThresholdForAllFactors rstar m k d K hd Nsel βfreq ρ₀ α θ θhost
            lamMatch aRow γrow ζSel lamSel ζSel smin τ tMatch ξMatch bMatch BO
            ζ χpair χlist σ χbal χbd χnbr χpairR χpath aEvent ∧
          OrdinaryWeightedCorrectionAfterLocalThresholds rstar d hd mAbs aAbs bAbs (2*mv) mv q₀ Ncorr Nc Ng Nh Ncol
            αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/εvortex) ∧
          OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq εvortex εabs εv ∧
        ∃Nhost:ℕ,2≤Nhost ∧ Nsel≤Nhost ∧ Ncorr≤Nhost ∧ Ngeom≤Nhost ∧ mv≤Nhost ∧
        ∀(n qCount D:ℕ),Nhost≤n→qCount≤n→
        ∀(F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2),
          (∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))→
          ρ₀ ≤ initialIndexDensity (Fin qCount) D→initialIndexDensity (Fin qCount) D≤1→
          (∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)→
        ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→(θhost+α)*(n:ℝ)≤D→
          OrdinaryOriginalDeepParentVortexBalanceBundleAt n qCount D rstar m k d K mv mAbs aAbs bAbs q₀ Nc Ng Nh Ncol hd
            βfreq ρ₀ α θ θhost lamMatch aRow γrow ζSel lamSel ζSel τ tMatch ξMatch bMatch σ ζ χpair χlist χbal χbd χnbr χpairR χpath aEvent
            εvortex εabs εv βv ξAbs χlocal χglobal χhub χcol BO F hF P
            Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
            kParent hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar χthree

theorem ordinary_presample_build_joint_vortex_bundle_separate_lists
    (L rstar d m k dMin:ℕ) (hdExt:2≤d) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (εvortex capHub ηBudget δAbs hAbs εabs εv ξedit ξAbs:ℝ)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (βv:ℝ)
    (hpre:OrdinaryOriginalPreSampleJointThresholdsSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv)
    (hε:0<εvortex) (hε1:εvortex≤1) (hερ:εvortex≤ρ₀/16) (hmv:0<mv)
    (hβv:0≤βv) (hβv1:βv≤1/4) (hβα:βv≤α/8)
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
    OrdinaryOriginalPreSampleJointVortexBundleSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget (α/2) (ρ₀*(βfreq/200)/2) (ρ₀/4) δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol
      βv Kdeep αcut c C a ε₀ ρdeep θdeep aLoad ξdeep bDeep Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut capDeep
      kParent hmParent βP ηP row ηH βH cParent Bparent εTri χhost δref href χref hpstar χthree ξedit ξAbs :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,hterminal,
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
    hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,hterminal,
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
