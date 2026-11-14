module

public import Mathlib.Tactic

@[expose] public section
/-! Positive event tolerances satisfying the shared failure and reference
bounds, selected after the constants they must lie below. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_reference_beta_choice
    (αRef βmax εBal εRef:ℝ)
    (hα:0<αRef) (hβ:0<βmax) (hBal:0<εBal) (hRef:0<εRef):
    ∃βQ:ℝ,0<βQ ∧ βQ≤1/4 ∧ βQ≤αRef/4 ∧ βQ≤βmax ∧ βQ≤εBal/4 ∧ βQ≤εRef/4:=by
  let βQ:=min (1/4:ℝ) (min (αRef/4) (min βmax (min (εBal/4) (εRef/4))))
  have hβQ:0<βQ:=by dsimp [βQ];positivity
  exact ⟨βQ,hβQ,min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩

theorem first_vortex_common_failure_choice (ε₀:ℝ) (hε:0<ε₀):
    ∃χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<ε₀:=by
  refine ⟨ε₀/16,ε₀/16,ε₀/16,ε₀/16,ε₀/16,ε₀/16,ε₀/16,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
end Oberwolfach
