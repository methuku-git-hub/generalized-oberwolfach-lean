module

public import Oberwolfach.MarkedVortexCutDeepHierarchy

@[expose] public section
/-! A deep-error bound chosen from fixed lower density bounds applies to the
actual graph and supplied marked-spoke density without changing the error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_deep_gap_uniform_transfer
    (rho0 rho tstar t omega xi:ℝ)
    (hrho0:0<rho0) (hrho:rho0≤rho) (ht:tstar≤t) (homega:0≤omega) (hxi:0≤xi)
    (hgap:(1+2/rho0)*xi≤tstar*omega/32):
    (1+2/rho)*xi≤t*omega/32:=by
  have hrhopos:0<rho:=hrho0.trans_le hrho
  have hinv:1/rho≤1/rho0:=by
    exact (one_div_le_one_div_of_le hrho0 hrho)
  have hleft:1+2/rho≤1+2/rho0:=by
    simp only [div_eq_mul_inv,one_mul] at hinv ⊢
    linarith only [hinv]
  have hmul:=mul_le_mul_of_nonneg_right hleft hxi
  have hright:=mul_le_mul_of_nonneg_right ht homega
  linarith
end Oberwolfach
