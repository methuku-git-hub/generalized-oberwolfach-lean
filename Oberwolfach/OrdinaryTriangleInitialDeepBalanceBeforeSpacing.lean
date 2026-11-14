module

public import Oberwolfach.OrdinaryVortexActualTraceCostAndRateBeforeSpacing
public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAtBeforeSpacing
public import Oberwolfach.OrdinaryActualInitialAmbientBalance
public import Oberwolfach.OrdinaryActualTraceBalanceBoundaryMonotone

@[expose] public section
/-! Choose one boundary coefficient before spacing for the initial and
later protected balances, independently of the wheel length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_initial_deep_balance_before_spacing
    (ρ₀ α pmin hmin:ℝ) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃cBoundary:ℝ,0<cBoundary ∧ ∀ε:ℝ,0<ε→ε<1/4→∀ηProfile ζ:ℝ,0<ηProfile→0<ζ→
    ∃δDeep rate:ℝ,0<δDeep ∧ δDeep≤α ∧ 0<rate ∧
    ∀ηInitial:ℝ,0<ηInitial→∃δInitial:ℝ,0<δInitial ∧ δInitial≤α ∧ δInitial≤ηInitial ∧
    ∀(d:ℕ),∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃mInitial mBalance:ℕ,1≤mInitial ∧ 1≤mBalance ∧
      OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial ∧
      OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cBoundary δDeep rate d 2 β C mBalance :=by
  obtain ⟨cI,hcI,hInitial⟩:=ordinary_vortex_initial_ambient_balance_at_choice_before_spacing
    ρ₀ α pmin hmin hρ₀ hα hpmin hhmin
  obtain ⟨cD,hcD,hDeep⟩:=ordinary_vortex_actual_trace_separated_cost_and_rate_before_spacing
    ρ₀ α pmin hmin 2 (by omega) hρ₀ hα hpmin hhmin
  let cBoundary:=min cI cD
  refine ⟨cBoundary,lt_min hcI hcD,?_⟩
  intro ε hε hεsmall ηProfile ζ hη hζ
  obtain ⟨δDeep,rate,hδDeep,hδα,hrate,hDeep⟩:=hDeep ε hε hεsmall ηProfile ζ hη hζ
  refine ⟨δDeep,rate,hδDeep,hδα,hrate,?_⟩
  intro ηInitial hηInitial
  obtain ⟨δInitial,hδInitial,hδIα,hδIη,hInitial⟩:=hInitial ε hε hεsmall ηInitial hηInitial
  refine ⟨δInitial,hδInitial,hδIα,hδIη,?_⟩
  intro d β hβ hβ1 hβI hβD C hC
  obtain ⟨mInitial,hmI,hI⟩:=hInitial d β hβ hβ1 hβI
  obtain ⟨mBalance,hmB,hB⟩:=hDeep d β hβ hβ1 hβD C hC
  have hB':OrdinaryActualTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηProfile ζ cD δDeep rate d 2 β C mBalance:=hB
  refine ⟨mInitial,mBalance,hmI,hmB,?_,?_⟩
  · apply ordinary_initial_ambient_balance_actual_of_reference ε ρ₀ α pmin hmin ηInitial cBoundary δInitial d β mInitial
    exact ordinary_vortex_initial_ambient_balance_at_monotone ε ρ₀ α pmin hmin ηInitial cBoundary cI δInitial δInitial
      d β mInitial mInitial hε.le (min_le_left _ _) le_rfl le_rfl hI
  · exact ordinary_actual_trace_balance_boundary_monotone ε ρ₀ α pmin hmin ηProfile ζ cBoundary cD δDeep rate
      d 2 β C mBalance mBalance hε.le (min_le_right _ _) le_rfl hB'
end Oberwolfach
