module

public import Oberwolfach.FirstVortexNoMarkedActiveClassChoices
public import Oberwolfach.FirstVortexGeometricActiveCeiling

@[expose] public section
/-! An explicit vortex-scale cap suffices for the geometric active bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_geometric_active_rate_of_scale
    (ρ ε cap:ℝ) (hρ:0<ρ) (hε:0<ε) (hcap:0<cap)
    (hsmall:ε≤cap*((ρ/4)/40000)/1024):
    8*((1/2:ℝ)*ε^2)/((ρ/4)/40000)<cap*ε/128 :=by
  let c:ℝ:=(ρ/4)/40000
  have hc:0<c:=by dsimp [c];positivity
  have hs:ε≤cap*c/1024:=hsmall
  change 8*((1/2:ℝ)*ε^2)/c<cap*ε/128
  apply (div_lt_iff₀ hc).2
  have hm:=mul_le_mul_of_nonneg_left hs (show 0≤4*ε by positivity)
  have hp:0<cap*ε*c:=by positivity
  nlinarith
end Oberwolfach
