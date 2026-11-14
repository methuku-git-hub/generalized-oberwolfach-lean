module

public import Oberwolfach.FirstVortexIndependentLoadBudgetEventually

@[expose] public section
/-! The assignment error can be chosen after the independent load and below
both the all-hub load allowance and the matching incidence allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_assignment_load_choice (ρ δsmall:ℝ) (hρ:0<ρ) (hδ:0<δsmall):
    ∃αAssign b:ℝ,0<αAssign ∧ 0<b ∧
      b≤((ρ/4)/40000)/16 ∧ αAssign/16≤b ∧ αAssign/16≤δsmall/4 :=by
  let b:=ρ/4000000
  let αAssign:=min (8*b) (2*δsmall)
  have hb:0<b:=by dsimp [b];positivity
  have hα:0<αAssign:=by dsimp [αAssign];positivity
  have hαb:αAssign≤8*b:=min_le_left _ _
  have hαδ:αAssign≤2*δsmall:=min_le_right _ _
  refine ⟨αAssign,b,hα,hb,?_,?_,?_⟩
  · dsimp [b];linarith
  · linarith
  · linarith
end Oberwolfach
