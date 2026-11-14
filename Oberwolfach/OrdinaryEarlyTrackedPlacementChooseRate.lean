module

public import Oberwolfach.OrdinaryEarlyUniformTrackedPlacementAtRate

@[expose] public section
/-! Expose the edit rate together with its deletion-uniform placement
callback before the sample and failure allowances are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_early_tracked_placement_choose_rate
    (d m:ℕ) (lam bList bRate εearly cBudget θ z a γ ζ bMatch α δ ζret κ ξcap:ℝ)
    (hshape:OrdinaryEarlyUniformTrackedPlacementShape d m lam bList bRate εearly cBudget θ z a γ ζ bMatch α δ ζret κ ξcap):
    ∃ξ:ℝ,0<ξ ∧ ξ≤bList/8 ∧ ξ≤bMatch ∧ ξ≤ξcap ∧
      OrdinaryEarlyUniformTrackedPlacementAtRate d m lam bList bRate εearly cBudget θ z a γ ζ bMatch α δ ζret κ ξ :=by
  exact hshape
end Oberwolfach
