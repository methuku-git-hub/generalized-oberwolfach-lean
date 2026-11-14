module

public import Oberwolfach.OrdinaryOriginalPreSampleWithEditRatesAt
public import Oberwolfach.OrdinaryMatchingCorrectionCommonThresholds
public import Oberwolfach.OrdinaryDeepEditRatesAfterCertificate

@[expose] public section
/-! Name the matching continuation while retaining the exact early placement
parameters, before the edit cap is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryOriginalPreSampleFixedThresholdsAt
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace ε:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (mv mAbs q₀:ℕ) (ζ χpair χlist χbal χbd χnbr χpairR χpath χlocal χglobal χhub χcol ξedit:ℝ):Prop :=
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
        ∃ξAbs:ℝ,
          0<ξedit ∧ ξedit≤capHub*εvortex/1000 ∧ ξedit≤ηBudget/1000 ∧ ξedit≤σ ∧ ξedit≤ζPlace/8 ∧ ξedit≤bMatch ∧
          OrdinaryEarlyUniformColumnsAtRate d m lamPlace ζPlace b ε cBudget θ z δ aRow γrow (θ/2) bMatch αCap ξedit ∧
          0<ξAbs ∧ ξAbs≤capHub*εvortex/1000 ∧ ξAbs≤ηBudget/1000 ∧ ξAbs≤σ ∧ ξAbs≤hAbs/100 ∧
          (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices rstar d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) ∧
        ∃aAbs bAbs:ℕ,∃aEvent:ℝ,0<aEvent ∧ ∃Nsel Ncorr Nc Ng Nh Ncol Ngeom:ℕ,
          1≤Ncorr ∧ 1≤Nc ∧ 1≤Ng ∧ 1≤Nh ∧ 1≤Ncol ∧ 1≤Ngeom ∧
          OrdinaryOriginalThresholdForAllFactors rstar m k d K hd Nsel βfreq ρ₀ α θ θhost
            lamMatch aRow γrow ζSel lamSel ζSel smin τ tMatch ξMatch bMatch BO
            ζ χpair χlist σ χbal χbd χnbr χpairR χpath aEvent ∧
          OrdinaryWeightedCorrectionAfterLocalThresholds rstar d hd mAbs aAbs bAbs (2*mv) mv q₀ Ncorr Nc Ng Nh Ncol
            αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs (θ/2) χlocal χglobal χhub χcol (2/εvortex) ∧
          OrdinaryFirstVortexCorrectionThresholdShape Ngeom Nc Ng Nh Ncol θhost α ρ₀ βfreq εvortex εabs εv
end Oberwolfach
