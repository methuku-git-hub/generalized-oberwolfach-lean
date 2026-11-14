module

public import Oberwolfach.OrdinaryDeepRowsCutsAfterEarly

@[expose] public section
/-! Select the deep wheel constants before choosing the vortex contraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem ordinary_deep_rows_cuts_choose_early
    (m:ℕ) (hm:3≤m) (α ρ₀ pmin αcut:ℝ)
    (hα:0<α) (hρ:0<ρ₀) (hp:0<pmin) (hp1:pmin≤1)
    (hcut:0<αcut) (hcut1:αcut≤1/2) (hcutα:αcut≤α/2):
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∃K:ℕ,0<K ∧ ∃a ε₀ ρ θdeep:ℝ,
      0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θdeep ∧
      OrdinaryDeepRowsCutsAfterEarly m K α ρ₀ pmin αcut c C a ε₀ ρ θdeep :=by
  exact ordinary_general_inner_deep_rows_cuts_before_spacing m hm α ρ₀ pmin αcut
    hα hρ hp hp1 hcut hcut1 hcutα
end Oberwolfach
