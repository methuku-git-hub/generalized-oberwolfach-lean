module

public import Oberwolfach.FirstVortexActualLocalChainRates

@[expose] public section
/-! The current local error estimate cannot be instantiated at a small
relative balance cap when it retains the global assignment allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_assignment_local_scale_obstruction
    (ε α αAssign tLocal cLocal rho b a γ κ:ℝ)
    (hε:0<ε) (hεα:ε≤α/1000) (hαAssign:αAssign/2=α)
    (hrho:0<rho) (hb:0≤b) (hmax:0≤max a γ) (hκ:0≤κ)
    (hBRate:b+2*max a γ+αAssign/16+κ<tLocal)
    (hLocalRate:(17+4/rho)*tLocal≤cLocal*ε/2):
    4250<cLocal :=by
  have hAssign:2000*ε≤αAssign:=by linarith
  have ht:0<tLocal:=by nlinarith
  have hLower:125*ε<tLocal:=by nlinarith
  have hExtra:0≤(4/rho)*tLocal:=by positivity
  have hScale:17*tLocal≤cLocal*ε/2:=by
    have heq:(17+4/rho)*tLocal=17*tLocal+(4/rho)*tLocal:=by ring
    rw [heq] at hLocalRate
    linarith
  nlinarith

/-- Even before the sufficient rate reduction, the displayed local rim
budget forces a large relative cap if its other terms are nonnegative. -/
theorem first_vortex_assignment_physical_local_obstruction
    (ε α αAssign n inner cLocal boundary m κ junk:ℝ)
    (hε:0<ε) (hn:0<n) (hεα:ε≤α/1000) (hαAssign:αAssign/2=α)
    (hc:0≤cLocal) (hinner:inner≤ε*n)
    (hb:0≤boundary) (hm:0≤m) (hκ:0≤κ) (hjunk:0≤junk)
    (hbudget:2*(boundary+2*m*n+(αAssign/16)*n+(κ*n+1))+junk≤cLocal*inner):
    250≤cLocal :=by
  have hAssign:2000*ε≤αAssign:=by linarith
  have hAssignN:=mul_le_mul_of_nonneg_right hAssign hn.le
  have hcap:=mul_le_mul_of_nonneg_left hinner hc
  have hmn:0≤m*n:=mul_nonneg hm hn.le
  have hκn:0≤κ*n:=mul_nonneg hκ hn.le
  have hsmall:(αAssign/8)*n≤cLocal*(ε*n):=by nlinarith
  have hpos:0<ε*n:=mul_pos hε hn
  nlinarith
end Oberwolfach
