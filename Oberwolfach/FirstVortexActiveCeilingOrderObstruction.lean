module

public import Oberwolfach.FirstVortexActiveAndClassCapChoices

@[expose] public section
/-! A diagnostic for the quantifier order of the active ceiling estimate.
Once the vortex error and matching density are fixed, that estimate cannot
hold for an arbitrarily small later active tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_active_ceiling_fixed_scale_lower_bound
    (ρ ε α θ lamAssign cap:ℝ)
    (hρ:0<ρ) (hε:0<ε) (hθ:0≤θ) (hAssign:0≤lamAssign)
    (hεα:ε≤α/1000)
    (hαθ:(2*α)/16≤((ρ/4)/40000)*θ/1024)
    (hRate:8*(θ*ε^2+lamAssign*ε)/((ρ/4)/40000)<cap*ε/128):
    131072000*ε^2<cap*((ρ/4)/40000)^2:=by
  let c:ℝ:=(ρ/4)/40000
  have hc:0<c:=by dsimp [c];positivity
  have hRate':8*(θ*ε^2+lamAssign*ε)/c<cap*ε/128:=hRate
  have hRateMul:1024*(θ*ε^2+lamAssign*ε)<cap*ε*c:=by
    have h:=(div_lt_iff₀ hc).mp hRate'
    nlinarith
  have hdrop:0≤1024*lamAssign*ε:=by positivity
  have hr:1024*θ*ε<cap*c:=by
    have h:1024*θ*ε^2<cap*ε*c:=by nlinarith
    nlinarith
  have ha:128000*ε≤c*θ:=by
    change (2*α)/16≤c*θ/1024 at hαθ
    linarith
  have hm:=mul_le_mul_of_nonneg_right ha (show 0≤1024*ε by positivity)
  have hn:=mul_lt_mul_of_pos_right hr hc
  change 131072000*ε^2<cap*c^2
  nlinarith
end Oberwolfach
