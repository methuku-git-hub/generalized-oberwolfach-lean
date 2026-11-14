module

public import Oberwolfach.FirstVortexOrderedGeometryHierarchy

@[expose] public section
/-! Reserve half of the global change budget for the global matching loss
while choosing the local outside-change rates independently. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_separate_eta_coarse_global_rates
    (globalCap rho t etaLocal δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b etaGlobal:ℝ)
    (hcap:0≤globalCap) (hrho:0<rho) (hLocalEta:0≤etaLocal)
    (hroom:2*(1+2/rho)*etaGlobal≤globalCap/2)
    (hlocal:FirstVortexLocalGeometryRateBounds (globalCap/2) rho t etaLocal δsmall δspoke
      ζret ηBalance θ a γ ξPart κ Δ b):
    2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+(1+2/rho)*etaGlobal)<globalCap ∧
    2*(ζret+10*θ)+ηBalance≤globalCap :=by
  have hrow:=hlocal.2.2.2.2.2.2.2.1
  have hcol:=hlocal.2.2.2.2.2.2.2.2
  have hterm:0≤(1+2/rho)*etaLocal:=by positivity
  constructor <;> nlinarith
end Oberwolfach
