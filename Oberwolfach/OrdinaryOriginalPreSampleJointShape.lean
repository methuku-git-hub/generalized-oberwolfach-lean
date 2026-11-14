module

public import Oberwolfach.OrdinaryOriginalSelectorPlacementJointShape
public import Oberwolfach.OrdinaryOriginalThresholdChooseMatchCore
public import Oberwolfach.OrdinarySelectedUniformEditBeforeAbsorber

@[expose] public section
/-! The joint selector and reserved-placement choices, kept as one named
interface so the correction parameters can be chosen earlier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach

def OrdinaryOriginalPreSampleJointShape
    (L rstar:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α):Prop :=
    let smin₀:=βfreq/200;let αCap:=5*ρ₀*smin₀^2/128;
    ∃m k:ℕ,∃βPlace lamPlace ζPlace ε:ℝ,∃dMin:ℕ,
      OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k ∧
      OrdinaryPlacementEarlyRateData γList ρ₀ smin₀ capInner βPlace lamPlace ζPlace ε dMin ∧
    ∃δ θ κ b z matchErr σ κ':ℝ,∃dNeed:ℕ,
      OrdinaryPlacementStage m dNeed αCap lamPlace ζPlace capEdit δ θ κ b z matchErr σ κ' ∧
    ∃βSel lamSel ζSel smin:ℝ,∃d K rank:ℕ,
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
          lamPlace ζPlace b ε cBudget θ z δ aRow γrow (θ/2) bMatch αCap
end Oberwolfach
