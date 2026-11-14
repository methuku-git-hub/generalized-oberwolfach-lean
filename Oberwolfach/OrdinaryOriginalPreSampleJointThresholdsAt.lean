module

public import Oberwolfach.OrdinaryOriginalPreSampleJointTerminalAt
public import Oberwolfach.OrdinaryMatchingCorrectionCommonThresholds

@[expose] public section
/-! Name the matching continuation while retaining the exact early placement
parameters, before the edit cap is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryOriginalPreSampleJointThresholdsAt
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace ε:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv:ℝ):Prop :=
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
            OrdinaryOriginalTerminalConditionalPreparationAt rstar m k d K hd βfreq ρ₀ α θhost εvortex βv
              δ θ aRow γrow σ lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs) ∧
        ∃aAbs bAbs:ℕ,∃aEvent:ℝ,0<aEvent ∧ ∃Nsel Ncorr Nc Ng Nh Ncol Ngeom:ℕ,
          1≤Ncorr ∧ 1≤Nc ∧ 1≤Ng ∧ 1≤Nh ∧ 1≤Ncol ∧ 1≤Ngeom ∧
          OrdinaryOriginalThresholdForAllFactors rstar m k d K hd Nsel βfreq ρ₀ α θ θhost
            lamMatch aRow γrow ζSel lamSel ζSel smin τ tMatch ξMatch bMatch BO
            ζ χpair χlist σ χbal χbd χnbr χpairR χpath aEvent ∧
          OrdinaryWeightedCorrectionAfterLocalThresholds rstar d hd mAbs aAbs bAbs (2*mv) mv q₀ Ncorr Nc Ng Nh Ncol
            αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/εvortex) ∧
          OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq εvortex εabs εv

theorem ordinary_presample_choose_joint_thresholds
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hρ1:ρ₀≤1) (hα:0<α) (hθhost:1/2≤θhost)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs βv:ℝ)
    (hpre:OrdinaryOriginalPreSampleJointTerminalAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs βv)
    (hε:0<εvortex) (habs:εvortex≤εabs) (hv:εvortex≤εv)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol:ℝ)
    (hζ:0<ζ) (hχpair:0<χpair) (hχlist:0<χlist) (hχbal:0<χbal) (hχbd:0<χbd)
    (hχnbr:0<χnbr) (hχpairR:0<χpairR) (hχpath:0<χpath) (hχlocal:0<χlocal)
    (hχglobal:0<χglobal) (hχhub:0<χhub) (hχcol:0<χcol):
    OrdinaryOriginalPreSampleJointThresholdsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv
      mv mAbs q₀ ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit ξAbs βv :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,hterminal⟩:=hpre
  have hθ:0<θ:=by obtain ⟨_,_,_,_,hθ,_⟩:=hStage; exact hθ
  have hσ:0<σ:=by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hσ,_⟩:=hStage; exact hσ
  obtain ⟨aAbs,bAbs,hcorr⟩:=hcorrAt mAbs
  obtain ⟨aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom⟩:=
    ordinary_matching_correction_common_thresholds rstar m k d K hd βfreq ρ₀ α θ θhost lamMatch aRow γrow ζSel lamSel ζSel smin
      τ tMatch ξMatch bMatch BO hChoice ζ χpair χlist σ χbal χbd χnbr χpairR χpath
      hζ hχpair hχlist hσ hχbal hχbd hχnbr hχpairR hχpath
      mAbs aAbs bAbs (2*mv) mv q₀ αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs εvortex hcorr
      hθhost hα hρ₀ hρ1 hβfreq hβ1 hε habs hv (θ/2) χlocal χglobal χhub χcol (2/εvortex)
      (by positivity) hχlocal hχglobal hχhub hχcol (by positivity)
  exact ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,hterminal,
    aAbs,bAbs,aEvent,haEvent,Nsel,Ncorr,Nc,Ng,Nh,Ncol,Ngeom,hNcorr,hNc,hNg,hNh,hNcol,hNgeom,hsel,hlocal,hgeom⟩
end Oberwolfach
