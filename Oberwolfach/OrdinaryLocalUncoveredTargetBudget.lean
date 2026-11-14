module

public import Oberwolfach.OrdinaryPlacementTargetFloorLocalRows

@[expose] public section

/-! A contraction fixed before θ controls the local unassigned targets
once the later placement rate has a positive proportional lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_local_uncovered_target_budget
    (n inner ε c θ z error fluct:ℝ)
    (hn:0≤n) (hθ:0≤θ) (hz0:0≤z) (hε:ε≤c/16) (hz:c*θ≤z)
    (hinner:inner≤ε*n) (herror:error≤z*n/16) (hfluct:fluct≤z*n/16):
    2*θ*inner+fluct+error≤z*n :=by
  have hfirst:=mul_le_mul_of_nonneg_left hinner (show 0≤2*θ by positivity)
  have hsecond:=mul_le_mul_of_nonneg_right hε hθ
  have hthird:=mul_le_mul_of_nonneg_right (show 2*θ*ε≤z/8 by nlinarith [hsecond,hz]) hn
  nlinarith only [hfirst,hthird,herror,hfluct,mul_nonneg hn hz0]
end Oberwolfach
