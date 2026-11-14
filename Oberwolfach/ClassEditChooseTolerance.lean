module

public import Mathlib.Tactic

@[expose] public section
/-! Reserve half the existing edge-error tolerance before choosing the
regularisation edit tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem class_edit_choose_tolerance (α ε lam:ℝ) (hα:0<α) (hε:0<ε) (hlam:0<lam):
    ∃ξ:ℝ,0<ξ ∧ ξ≤α/32 ∧ ξ/2≤(lam-lam/2)*ε:=by
  let ξ:=min (α/64) (lam*ε/2)
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hαξ:ξ≤α/64:=min_le_left _ _
  have hlξ:ξ≤lam*ε/2:=min_le_right _ _
  have hp:0<lam*ε:=mul_pos hlam hε
  refine ⟨ξ,hξ,?_,?_⟩ <;> nlinarith
end Oberwolfach
