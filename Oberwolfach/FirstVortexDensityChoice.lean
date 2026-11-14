module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_density_choice
    (ρ₀ α C εAbs εMax:ℝ) (hρ:0<ρ₀) (hα:0<α) (hC:0<C) (hAbs:0<εAbs) (hMax:0<εMax):
    ∃ε:ℝ,0<ε ∧ ε<1/4 ∧ ε≤εAbs ∧ ε≤εMax ∧ ε≤ρ₀/80000 ∧ ε≤α/(1000*C):=by
  let ε:ℝ:=min (1/8) (min εAbs (min εMax (min (ρ₀/80000) (α/(1000*C)))))
  have hε:0<ε:=by dsimp [ε];positivity
  have h8:ε≤1/8:=min_le_left _ _
  have hAbs':ε≤εAbs:=(min_le_right _ _).trans (min_le_left _ _)
  have hMax':ε≤εMax:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ':ε≤ρ₀/80000:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hα':ε≤α/(1000*C):=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  exact ⟨ε,hε,by linarith,hAbs',hMax',hρ',hα'⟩
end Oberwolfach
