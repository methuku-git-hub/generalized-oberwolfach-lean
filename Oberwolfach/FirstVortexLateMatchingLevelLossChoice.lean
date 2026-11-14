module

public import Mathlib.Tactic

@[expose] public section
/-! The matching selector can use positive loss budgets below both the
previously fixed level budgets and its later ordinary-list allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_late_matching_level_loss_choice
    (γLevel σLevel ζOrd:ℝ) (hγ:0<γLevel) (hσ:0<σLevel) (hζ:0<ζOrd):
    ∃γMatch σMatch:ℝ,0<γMatch ∧ 0<σMatch ∧
      γMatch≤γLevel ∧ σMatch≤σLevel ∧ γMatch≤ζOrd/2 :=by
  let γMatch:=min (γLevel/2) (ζOrd/4)
  let σMatch:=σLevel/2
  have hγm:0<γMatch:=by dsimp [γMatch];positivity
  have hσm:0<σMatch:=by dsimp [σMatch];positivity
  have hγlevel:γMatch≤γLevel:=by dsimp [γMatch];have hh:=min_le_left (γLevel/2) (ζOrd/4);linarith
  have hσlevel:σMatch≤σLevel:=by dsimp [σMatch];linarith
  have hγζ:γMatch≤ζOrd/2:=by dsimp [γMatch];have hh:=min_le_right (γLevel/2) (ζOrd/4);linarith
  exact ⟨γMatch,σMatch,hγm,hσm,hγlevel,hσlevel,hγζ⟩
end Oberwolfach
