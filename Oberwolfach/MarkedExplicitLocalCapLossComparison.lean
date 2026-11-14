module

public import Oberwolfach.MarkedExplicitJointBalanceBoundaryBudget

@[expose] public section
/-! Sufficient quantitative balance windows for the separated global loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_explicit_local_cap_loss_comparison
    (m h:ℕ) (etaBal x rho δsmall:ℝ) (hrho:0<rho)
    (hBoundary:640*((h:ℝ)+1)*δsmall≤rho*x)
    (hAmbient:640*((m+4:ℕ):ℝ)*δsmall≤rho*x)
    (hRelative:640*((m+4:ℕ):ℝ)*δsmall≤rho*etaBal):
    40*δsmall≤markedExplicitJointLocalCap m h etaBal x*rho :=by
  have hh:0<16*((h:ℝ)+1):=by positivity
  have hm:0<16*((m+4:ℕ):ℝ):=by positivity
  have h1:40*δsmall/rho≤x/(16*((h:ℝ)+1)):=by
    apply (div_le_div_iff₀ hrho hh).2
    nlinarith [hBoundary]
  have h2:40*δsmall/rho≤x/(16*((m+4:ℕ):ℝ)):=by
    apply (div_le_div_iff₀ hrho hm).2
    nlinarith [hAmbient]
  have h3:40*δsmall/rho≤etaBal/(16*((m+4:ℕ):ℝ)):=by
    apply (div_le_div_iff₀ hrho hm).2
    nlinarith [hRelative]
  have hc:40*δsmall/rho≤markedExplicitJointLocalCap m h etaBal x:=by
    dsimp [markedExplicitJointLocalCap]
    exact le_min h1 (le_min h2 h3)
  exact (div_le_iff₀ hrho).mp hc
end Oberwolfach
