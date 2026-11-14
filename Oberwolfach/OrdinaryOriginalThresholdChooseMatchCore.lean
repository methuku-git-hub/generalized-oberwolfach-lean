module

public import Oberwolfach.OrdinaryOriginalThresholdAfterMatchChoice

@[expose] public section
/-! Choose the matching tolerances and deletion budget before probability
losses, the factor family and the sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_original_threshold_choose_match_core
    (rstar m k d K:ℕ) (hd:2 ≤ d) (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel smin:ℝ)
    (BO:Fin K → ℝ)
    (hselect:OrdinaryOriginalThresholdAfterMatchingRates rstar m k d K hd βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel smin BO):
    ∃τ t ξ b:ℝ,OrdinaryOriginalThresholdAfterMatchChoice rstar m k d K hd βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel smin τ t ξ b BO :=by
  exact hselect
end Oberwolfach
