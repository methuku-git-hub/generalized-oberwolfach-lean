module

public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAt
public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceUniformBeforeSpacing

@[expose] public section
/-! Initial-balance tolerances can be selected uniformly before the spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_initial_ambient_balance_at_choice_before_spacing
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃c:ℝ,0<c ∧ ∀ε:ℝ,0<ε→ε<1/4→∀η:ℝ,0<η→
    ∃δ:ℝ,0<δ ∧ δ≤α ∧ δ≤η ∧ ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δ→
    ∃m₀:ℕ,1≤m₀ ∧ OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin η c δ d β m₀ :=by
  exact ordinary_vortex_initial_ambient_balance_uniform_before_spacing ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
end Oberwolfach
