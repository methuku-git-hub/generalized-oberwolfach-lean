module

public import Oberwolfach.OrdinaryEarlyUniformColumnsChooseSmaller
public import Oberwolfach.OrdinaryCorrectionRateBeforeAbsorberUnderCap

@[expose] public section
/-! After the initial certificate tolerance is known, shrink the matching
and correction edit rates while retaining the previously fixed event cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_edit_rates_after_certificate
    (rstar d mMatch:ℕ) (hd:2≤d) (ε cap ηedit capExtra:ℝ)
    (hε:0<ε) (hcap:0<cap) (hη:0<ηedit) (hExtra:0<capExtra)
    (lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace:ℝ)
    (hcolumns:OrdinaryEarlyUniformColumnsBeforeAbsorberShape d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace)
    (αcorr pstar ω δAbs hAbs εabs εv:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly rstar αcorr pstar ω δAbs hAbs εabs εv):
    ∃ξedit ξAbs:ℝ,
      0<ξedit ∧ ξedit≤cap*ε/1000 ∧ ξedit≤ηedit/1000 ∧ ξedit≤capExtra ∧ ξedit≤bList/8 ∧ ξedit≤bMatch ∧
      OrdinaryEarlyUniformColumnsAtRate d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace ξedit ∧
      0<ξAbs ∧ ξAbs≤cap*ε/1000 ∧ ξAbs≤ηedit/1000 ∧ ξAbs≤capExtra ∧ ξAbs≤hAbs/100 ∧
      (∀mAbs:ℕ,∃aAbs bAbs:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices rstar d hd mAbs aAbs bAbs αcorr pstar ω εabs εv (2*((3*d:ℕ):ℝ)) ξAbs) :=by
  let capChosen:=min (cap*ε/1000) (min (ηedit/1000) capExtra)
  have hChosen:0<capChosen:=by dsimp [capChosen]; positivity
  obtain ⟨ξedit,hξ,hξcap,hξlist,hξmatch,hcolumns⟩:=ordinary_early_uniform_columns_choose_smaller
    d mMatch lam bList bRate εearly cBudget θ z δplace aRow γrow ζlocal bMatch αplace capChosen hChosen hcolumns
  obtain ⟨ξAbs,hAbs0,hAbsCap,hAbsH,hcorr⟩:=ordinary_correction_rate_before_absorber_under_cap
    rstar d hd αcorr pstar ω δAbs hAbs εabs εv (2*((3*d:ℕ):ℝ)) capChosen hcorr (by positivity) hChosen
  have hA:capChosen≤cap*ε/1000:=min_le_left _ _
  have hB:capChosen≤ηedit/1000:=(min_le_right _ _).trans (min_le_left _ _)
  have hC:capChosen≤capExtra:=(min_le_right _ _).trans (min_le_right _ _)
  exact ⟨ξedit,ξAbs,hξ,hξcap.trans hA,hξcap.trans hB,hξcap.trans hC,hξlist,hξmatch,hcolumns,
    hAbs0,hAbsCap.trans hA,hAbsCap.trans hB,hAbsCap.trans hC,hAbsH,hcorr⟩
end Oberwolfach
