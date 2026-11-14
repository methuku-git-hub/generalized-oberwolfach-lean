module

public import Oberwolfach.OrdinaryOriginalThresholdForAllFactors

@[expose] public section
/-! Select the original weighted-event threshold before the factor family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_original_threshold_choose_factor_threshold
    (rstar m k d K:ℕ) (hd:2 ≤ d) (βfreq ρ₀ α θ θhost lam aRow γ cap lamList ζDel smin τ t ξ b:ℝ)
    (BO:Fin K → ℝ) (ζ χpair χlist σ χbal χbd χnbr χpairR χpath:ℝ)
    (hselect:OrdinaryOriginalThresholdAfterLosses rstar m k d K hd βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel smin τ t ξ b BO ζ χpair χlist σ χbal χbd χnbr χpairR χpath):
    ∃a:ℝ,0<a ∧ ∃N:ℕ,OrdinaryOriginalThresholdForAllFactors rstar m k d K hd N βfreq ρ₀ α θ θhost
      lam aRow γ cap lamList ζDel smin τ t ξ b BO ζ χpair χlist σ χbal χbd χnbr χpairR χpath a :=by
  exact hselect
end Oberwolfach
