module

public import Oberwolfach.OrdinaryInitialDeepBalanceCommonBoundary
public import Oberwolfach.OrdinaryVortexBufferedTraceSeparatedLinearCostAndRate

@[expose] public section
/-! Choose the initial and deep-trace balance parameters in a common
pre-sampling order, with one boundary rate and one host-size threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_deep_balance_ordered_choice
    (ρ₀ α pmin hmin:ℝ) (d buffer:ℕ) (hbuffer:2≤buffer) (hρ₀:0<ρ₀)
    (hα:0<α) (hpmin:0<pmin) (hhmin:0<hmin):
    ∃c:ℝ,0<c ∧ ∀ε:ℝ,0<ε→ε<1/4→∀ηinitial ηdeep ζ:ℝ,0<ηinitial→0<ηdeep→0<ζ→
    ∃δInitial δDeep rate:ℝ,0<δInitial ∧ δInitial≤α ∧ δInitial≤ηinitial ∧
      0<δDeep ∧ δDeep≤α ∧ 0<rate ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δInitial→β≤δDeep→∀C:ℝ,0≤C→
    ∃m₀:ℕ,1≤m₀ ∧
      OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin ηinitial c δInitial d β m₀ ∧
      OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin ηdeep ζ c δDeep rate d buffer β C m₀ :=by
  obtain ⟨cI,hcI,hI⟩:=ordinary_vortex_initial_ambient_balance_at_choice ρ₀ α pmin hmin d hρ₀ hα hpmin hhmin
  obtain ⟨cD,hcD,hD⟩:=ordinary_vortex_buffered_trace_separated_linear_cost_and_rate
    ρ₀ α pmin hmin d buffer hbuffer hρ₀ hα hpmin hhmin
  refine ⟨min cI cD,lt_min hcI hcD,?_⟩
  intro ε hε hε1 ηinitial ηdeep ζ hηinitial hηdeep hζ
  obtain ⟨δI,hδI,hδIα,hδIη,hI⟩:=hI ε hε hε1 ηinitial hηinitial
  obtain ⟨δD,rate,hδD,hδDα,hrate,hD⟩:=hD ε hε hε1 ηdeep ζ hηdeep hζ
  refine ⟨δI,δD,rate,hδI,hδIα,hδIη,hδD,hδDα,hrate,?_⟩
  intro β hβ hβ1 hβI hβD C hC
  obtain ⟨mI,hmI,hI⟩:=hI β hβ hβ1 hβI
  obtain ⟨mD,hmD,hD⟩:=hD β hβ hβ1 hβD C hC
  refine ⟨max mI mD,by omega,?_,?_⟩
  · exact ordinary_vortex_initial_ambient_balance_at_monotone ε ρ₀ α pmin hmin ηinitial
      (min cI cD) cI δI δI d β mI (max mI mD)
      hε.le (min_le_left _ _) le_rfl (le_max_left _ _) hI
  · exact ordinary_deep_trace_separated_balance_boundary_monotone ε ρ₀ α pmin hmin ηdeep ζ
      (min cI cD) cD δD rate d buffer β C mD (max mI mD)
      hε.le (min_le_right _ _) (le_max_right _ _) hD
end Oberwolfach
