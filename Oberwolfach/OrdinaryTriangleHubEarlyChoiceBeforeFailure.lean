module

public import Oberwolfach.OrdinaryTriangleHubEarlyBeforeFailure

@[expose] public section
/-! Choose the triangle cover and hub constants before contraction and failures. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_hub_early_choice_before_failure
    (α ρ₀ pmin cap:ℝ) (hα:0<α) (hρ:0<ρ₀) (hp:0<pmin) (hp1:pmin≤1) (hcap:0<cap):
    ∃κ c C:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ 0<c ∧ 0<C ∧ OrdinaryTriangleHubEarlyBeforeFailure α ρ₀ pmin κ c C :=by
  exact ordinary_triangle_hub_rows_cuts_before_failure α ρ₀ pmin cap hα hρ hp hp1 hcap
end Oberwolfach
