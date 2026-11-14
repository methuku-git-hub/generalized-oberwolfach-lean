module

public import Oberwolfach.FirstVortexLossScaleObstruction

@[expose] public section
/-! A necessary comparison between the early global load scale and the
later balance window for the separated-loss route. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_separate_loss_requires_balance_window
    (r:ℕ) (x etaBal δsmall cLocal rho etaGlobal:ℝ)
    (hx:0<x) (hηBal:0<etaBal) (hδ:0<δsmall) (hrho:0<rho)
    (hLocalEq:cLocal=Classical.choose (marked_vortex_initial_balance_from_parent_joint_local_changes r x hx etaBal hηBal))
    (hLoss:2*δsmall<etaGlobal) (hEta:etaGlobal≤cLocal*rho/4):
    64*((r+12:ℕ):ℝ)*δsmall<rho*x :=by
  have hc:0<cLocal:=by rw [hLocalEq];exact (Classical.choose_spec (marked_vortex_initial_balance_from_parent_joint_local_changes r x hx etaBal hηBal)).1
  have hcsmall:2*((r+12:ℕ):ℝ)*cLocal≤x/4:=by
    rw [hLocalEq];exact (Classical.choose_spec (marked_vortex_initial_balance_from_parent_joint_local_changes r x hx etaBal hηBal)).2.1
  have hdiff:8*δsmall<cLocal*rho:=by linarith
  have hmult:=mul_lt_mul_of_pos_left hdiff (show 0<8*((r+12:ℕ):ℝ) by positivity)
  have hscale:=mul_le_mul_of_nonneg_right hcsmall hrho.le
  nlinarith
end Oberwolfach
