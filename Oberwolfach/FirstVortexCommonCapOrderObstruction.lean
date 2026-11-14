module

public import Oberwolfach.FirstVortexOrderedGeometryHierarchy

@[expose] public section
/-! Diagnostic for combining the standard common-event perturbation slack
with a global correction rate and the vortex inner-density hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_common_cap_order_obstruction
    (ε δsmall cap κ ω:ℝ)
    (hε:0<ε) (hκ0:0≤κ) (hκ1:κ≤1) (hω:0≤ω)
    (hωε:ω≤ε/8) (hcap:cap≤κ*ω/8)
    (hglobal:4*δsmall≤cap) (hεsmall:ε<δsmall/4):False:=by
  have hprod:0≤(1-κ)*ω:=mul_nonneg (by linarith) hω
  nlinarith
theorem first_vortex_common_cap_row_rate_obstruction
    (ε δsmall cap κ ω rho tLocal eta δspoke ζret ηBalance θ a γ ξPart κerr Δ b:ℝ)
    (hε:0<ε) (hκ0:0≤κ) (hκ1:κ≤1) (hω:0≤ω) (hωε:ω≤ε/8)
    (hcap:cap≤κ*ω/8) (hεsmall:ε<δsmall/4)
    (hrho:0<rho) (heta:0≤eta) (hspoke:0≤δspoke) (hret:0≤ζret)
    (hbal:0≤ηBalance) (hθ:0≤θ) (ha:0≤a) (hξ:0≤ξPart) (hκerr:0≤κerr) (hΔ:0≤Δ)
    (hrate:FirstVortexLocalGeometryRateBounds cap rho tLocal eta δsmall δspoke ζret ηBalance θ a γ ξPart κerr Δ b):False:=by
  have hrow:=hrate.2.2.2.2.2.2.2.1
  have hmax:0≤max a (4*γ):=le_trans ha (le_max_left _ _)
  have hsq:0≤Real.sqrt δspoke:=Real.sqrt_nonneg _
  have hterm:0≤(1+2/rho)*eta:=by positivity
  have hglobal:4*δsmall≤cap:=by nlinarith
  exact first_vortex_common_cap_order_obstruction ε δsmall cap κ ω hε hκ0 hκ1 hω hωε hcap hglobal hεsmall
end Oberwolfach
