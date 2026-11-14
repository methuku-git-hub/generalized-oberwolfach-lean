module

public import Mathlib.Tactic

@[expose] public section
/-! The global change margin has room for the inner-set matching error
using only the original upper bound on that error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_separate_eta_global_room
    (globalCap rho ε etaGlobal:ℝ)
    (hrho:0<rho) (hε:0≤ε) (heta:etaGlobal≤rho) (hεcap:ε≤globalCap/4):
    2*(ε*etaGlobal/rho)≤globalCap/2 :=by
  have hmul:=mul_le_mul_of_nonneg_left heta hε
  have hquot:ε*etaGlobal/rho≤ε:=by
    apply (div_le_iff₀ hrho).2
    nlinarith
  linarith
end Oberwolfach
