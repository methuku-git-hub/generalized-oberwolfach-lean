module

public import Oberwolfach.OrdinaryOriginalPreSampleFixedJointRatesAt
public import Oberwolfach.OrdinaryOriginalTerminalConditionalPreparationSeparateListsNamed
public import Oberwolfach.OrdinaryDeepEditRatesAfterCertificate

@[expose] public section
/-! Name the matching continuation while retaining the exact early placement
parameters, before the edit cap is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryOriginalPreSampleJointTerminalSeparateListsAt
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace ε:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs βv:ℝ):Prop :=
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
          ∀rate ξroot:ℝ,0≤rate→0≤ξroot→∀mAbs tAbs aAbs bAbs:ℕ,
            OrdinaryOriginalTerminalConditionalPreparationSeparateListsAt rstar m k d K hd βfreq ρ₀ α θhost εvortex βv
              δ θ aRow γrow σ lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs

theorem ordinary_original_presample_joint_terminal_separate_lists_at
    (L rstar d m k dMin:ℕ) (βfreq ρ₀ α γList capInner capEdit θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs βv:ℝ)
    (hjoint:OrdinaryOriginalPreSampleFixedJointRatesAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs)
    (hm:7≤m) (hθhost:1/2≤θhost) (hε:0<εvortex) (hεearly:εvortex≤εearly)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin):
    OrdinaryOriginalPreSampleJointTerminalSeparateListsAt L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
      hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly εvortex capHub ηBudget αcorr pstar ω δAbs hAbs εabs εv ξedit ξAbs βv :=by
  obtain ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt⟩:=hjoint
  have hdMin:dMin≤d:=by
    obtain ⟨_,_,_,_,_,_,hdMin,_⟩:=hSpacing
    exact hdMin
  have hK:0<K:=by
    obtain ⟨_,_,_,_,_,_,_,_,_,hK,_⟩:=hSpacing
    omega
  have hda:1/θ≤(d:ℝ):=by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hda,_⟩:=hSpacing
    exact hda
  refine ⟨δ,θ,κ,b,z,matchErr,σ,κ',dNeed,hStage,βSel,lamSel,ζSel,smin,K,rank,hSpacing,
    ζret,N,lamMatch,aRow,γrow,BO,hAfter,hMatching,hBO,hd,hSelect,τ,tMatch,ξMatch,bMatch,hChoice,hColumns,
    hξedit,hξcap,hξη,hξσ,hξlist,hξmatch,hcolumnsAt,hξAbs,hξAbscap,hξAbsη,hξAbsσ,hξAbsh,hcorrAt,?_⟩
  intro rate ξroot hrate hξroot mAbs tAbs aAbs bAbs
  exact ordinary_original_terminal_conditional_preparation_separate_lists_named rstar m k d K dMin dNeed N hm hd hK hdMin
    βfreq ρ₀ α θhost capInner βPlace lamPlace ζPlace εearly εvortex βv hβfreq hρ₀ hα hθhost hε hεearly hEarly
    capEdit δ θ κ b z matchErr σ κ' ζret lamMatch aRow γrow ξedit bMatch hStage hAfter hMatching hda hcolumnsAt
    hξedit (by omega) rate ξroot hrate hξroot mAbs tAbs aAbs bAbs
end Oberwolfach
