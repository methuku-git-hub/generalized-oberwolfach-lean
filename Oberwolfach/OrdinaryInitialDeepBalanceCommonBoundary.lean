module

public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAt
public import Oberwolfach.OrdinaryDeepTraceSeparatedBalanceBoundaryMonotone

@[expose] public section
/-! The initial protected sample and the subsequent deep trace can use a
single boundary coefficient and host-size threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_deep_balance_common_boundary
    (ε ρ₀ α pmin hmin ηinitial ηdeep ζ cInitial cDeep δInitial δDeep rate:ℝ)
    (d buffer:ℕ) (β C:ℝ) (mInitial mDeep:ℕ)
    (hε:0≤ε) (hcInitial:0<cInitial) (hcDeep:0<cDeep)
    (hInitial:OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηinitial cInitial δInitial d β mInitial)
    (hDeep:OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηdeep ζ cDeep δDeep rate d buffer β C mDeep):
    ∃c:ℝ,0<c ∧ ∃m:ℕ,
      OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηinitial c δInitial d β m ∧
      OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηdeep ζ c δDeep rate d buffer β C m :=by
  refine ⟨min cInitial cDeep,lt_min hcInitial hcDeep,max mInitial mDeep,?_,?_⟩
  · exact ordinary_vortex_initial_ambient_balance_at_monotone ε ρ₀ α pmin hmin ηinitial
      (min cInitial cDeep) cInitial δInitial δInitial d β mInitial (max mInitial mDeep)
      hε (min_le_left _ _) le_rfl (le_max_left _ _) hInitial
  · exact ordinary_deep_trace_separated_balance_boundary_monotone ε ρ₀ α pmin hmin ηdeep ζ
      (min cInitial cDeep) cDeep δDeep rate d buffer β C mDeep (max mInitial mDeep)
      hε (min_le_right _ _) (le_max_right _ _) hDeep
end Oberwolfach
