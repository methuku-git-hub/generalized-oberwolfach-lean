module

public import Oberwolfach.OrdinaryOriginalThresholdAfterMatchingRates

@[expose] public section
/-! Fix the placement-compatible matching rates while retaining the
original weighted matching selector and its remaining quantifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_threshold_choose_matching_rates
    (rstar m k d K rank:ℕ) (hd:2 ≤ d)
    (βfreq ρ₀ α θ βList lamList ζDel smin:ℝ)
    (hpost:OrdinaryOriginalThresholdAfterSpacing rstar m k d K rank βfreq ρ₀ α θ βList lamList ζDel smin)
    (θhost:ℝ) (hθhost:1/2 ≤ θhost)
    (lam aRow γ cap:ℝ) (hlam:0<lam) (hlam1:lam ≤ 1) (ha:0<aRow) (hγ:0<γ) (hcap:0<cap)
    (haBound:aRow ≤ θ/(1600*(K:ℝ)*(K:ℝ))) (hslack:lam+γ*(1-θ+lam)<θ):
    ∃BO:Fin K → ℝ,(∀i,0<BO i) ∧
      OrdinaryOriginalThresholdAfterMatchingRates rstar m k d K hd βfreq ρ₀ α θ θhost
        lam aRow γ cap lamList ζDel smin BO :=by
  obtain ⟨BO,hBO,hselect⟩:=hpost hd θhost hθhost
  exact ⟨BO,hBO,hselect lam aRow γ cap hlam hlam1 ha hγ hcap haBound hslack⟩
end Oberwolfach
