module

public import Mathlib.Tactic

@[expose] public section
/-! Select the geometric parent coefficients before the vortex scale while
keeping the resulting profile errors within the scaled initial tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_parent_margins_before_vortex
    (cBoundary cProfile:ℝ) (hBoundary:0<cBoundary) (hProfile:0<cProfile):
    ∃γ eParent hParent:ℝ,
      0<γ ∧ 0<eParent ∧ 0<hParent ∧ γ≤eParent ∧
      eParent≤cBoundary ∧ hParent≤cBoundary ∧ eParent≤cProfile ∧ hParent≤cProfile ∧
      ∀ε:ℝ,0≤ε→eParent*ε≤cProfile*ε ∧ hParent*ε≤cProfile*ε :=by
  let a:ℝ:=min cBoundary cProfile/2
  have ha:0<a:=by dsimp [a];positivity
  have hab:a≤cBoundary:=by have hh:=min_le_left cBoundary cProfile;dsimp [a];linarith
  have hap:a≤cProfile:=by have hh:=min_le_right cBoundary cProfile;dsimp [a];linarith
  refine ⟨a/2,a,a,by positivity,ha,ha,by linarith,hab,hab,hap,hap,?_⟩
  intro ε hε
  exact ⟨mul_le_mul_of_nonneg_right hap hε,mul_le_mul_of_nonneg_right hap hε⟩
end Oberwolfach
