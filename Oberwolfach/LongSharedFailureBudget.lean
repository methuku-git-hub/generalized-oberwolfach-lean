module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the long common-event failure parameters from the requested
original probability error, leaving room for all eight local test losses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_shared_failure_budget (χ:ℝ) (hχ:0<χ) (hχ1:χ<1):
    ∃ ε₀ ηEvent χtest:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧ 0<χtest ∧
      0<1-(36*(ε₀+6*ηEvent)+ηEvent) ∧
      36*(ε₀+6*ηEvent)+ηEvent≤χ/2 ∧
      ∀εExtra:ℝ,0<εExtra→4*εExtra≤ε₀→
        χtest+χtest+χtest+2*χtest+χtest+χtest+χtest+εExtra<ε₀ :=by
  refine ⟨χ/100,χ/10000,χ/3200,by positivity,by linarith,by positivity,by positivity,?_,?_,?_⟩
  · linarith
  · linarith
  · intro εExtra _ hExtra
    linarith
end Oberwolfach
