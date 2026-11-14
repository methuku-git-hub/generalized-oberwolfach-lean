module

public import Oberwolfach.OrdinaryTriangleRowsCutsAfterEarly

@[expose] public section
/-! Select the triangle event cap before the contraction and sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_rows_cuts_choose_early
    (α ρ₀ pmin cap:ℝ) (hα:0<α) (hρ:0<ρ₀) (hp:0<pmin) (hp1:pmin≤1) (hcap:0<cap):
    ∃κ:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ OrdinaryTriangleRowsCutsAfterEarly α ρ₀ pmin κ :=by
  exact ordinary_triangle_fine_rows_cuts_product_prior α ρ₀ pmin cap hα hρ hp hp1 hcap
end Oberwolfach
