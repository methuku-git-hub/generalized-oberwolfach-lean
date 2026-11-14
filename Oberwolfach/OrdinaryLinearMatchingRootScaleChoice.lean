module

public import Oberwolfach.OrdinarySharpLinearRootScaleBeforeSampling

@[expose] public section
/-! A matching capacity proportional to the vortex scale can dominate a
quadratic root scale. All constants here are fixed before the vortex scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_linear_matching_root_scale_choice
    (m:ℕ) (root edit eCoeff hCoeff εcap c:ℝ)
    (hroot:0<root) (hedit:0<edit) (he:0<eCoeff) (hh:0<hCoeff) (hεcap:0<εcap) (hc:0<c):
    ∃ε lam βe βh θmatch:ℝ,0<ε ∧ ε≤εcap ∧ ε<1/4 ∧ lam=2*ε^2 ∧ 0<lam ∧ lam≤root ∧ lam≤1/4 ∧
      βe=eCoeff*ε ∧ βh=hCoeff*ε ∧ 0<βe ∧ 0<βh ∧
      lam≤βe/4 ∧ lam≤βh/2 ∧ 3*lam≤edit/4 ∧ lam*((m:ℝ)+1)≤edit/4 ∧
      θmatch=c*ε ∧ 0<θmatch ∧ 100*((m:ℝ)+2)*lam≤θmatch/64:=by
  let M:ℝ:=(m:ℝ)+2
  have hM:0<M:=by dsimp [M];positivity
  let cap:ℝ:=min εcap (c/(12800*M))
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨ε,lam,βe,βh,hε,hεsmall,hε1,hlameq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,hlame,hlamh,hrow,hlevel⟩:=
    ordinary_sharp_linear_root_scale_before_sampling m root edit eCoeff hCoeff cap hroot hedit he hh hcap
  have hεcap':ε≤εcap:=hεsmall.trans (min_le_left _ _)
  have hεc:ε≤c/(12800*M):=hεsmall.trans (min_le_right _ _)
  have hmul:ε*(12800*M)≤c:=(le_div_iff₀ (by positivity:0<12800*M)).mp hεc
  have hmul':(ε*(12800*M))*ε≤c*ε:=mul_le_mul_of_nonneg_right hmul hε.le
  refine ⟨ε,lam,βe,βh,c*ε,hε,hεcap',hε1,hlameq,hlam,hlamroot,hlam1,hβeeq,hβheq,hβe,hβh,
    hlame,hlamh,hrow,hlevel,rfl,mul_pos hc hε,?_⟩
  rw [hlameq]
  dsimp [M] at hmul'
  nlinarith only [hmul']
end Oberwolfach
