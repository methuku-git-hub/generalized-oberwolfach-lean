module

public import Oberwolfach.FirstVortexLocalChainRateChoice
public import Oberwolfach.FirstVortexOrderedGeometryHierarchy

@[expose] public section
/-! Choose the outside-change rate independently, and reserve half of the
global budget for the matching error on the smaller inner set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_separate_eta_local_rate_choice
    (upper c ε rho:ℝ) (hupper:0<upper) (hc:0<c) (hε:0<ε) (hrho:0<rho):
    ∃t:ℝ,0<t ∧ t≤upper ∧ (17+2/rho)*t≤c*ε/4 :=by
  obtain ⟨t,ht,htupper,hrate⟩:=first_vortex_local_chain_rate_choice upper (c/2) ε rho hupper (by positivity) hε hrho
  have hh:0≤(2/rho)*t:=by positivity
  have heq:(17+4/rho)*t=(17+2/rho)*t+(2/rho)*t:=by ring
  rw [heq] at hrate
  refine ⟨t,ht,htupper,?_⟩
  nlinarith

theorem first_vortex_separate_eta_global_rates
    (globalCap rho t etaLocal δsmall δspoke ζret ηBalance θ a γ ξPart κ Δ b ε etaGlobal:ℝ)
    (hrho:0<rho) (hcap:0≤globalCap) (hLocalEta:0≤etaLocal)
    (hroom:2*(ε*etaGlobal/rho)≤globalCap/2)
    (hlocal:FirstVortexLocalGeometryRateBounds (globalCap/2) rho t etaLocal δsmall δspoke
      ζret ηBalance θ a γ ξPart κ Δ b):
    2*(ζret+δspoke+Real.sqrt δspoke)+ηBalance+
      2*(2*θ+2*max a (4*γ)+2*ξPart+2*(δsmall+κ)+2*Δ+
        (etaLocal+(ε*etaGlobal+etaLocal)/rho))<globalCap ∧
    2*(ζret+10*θ)+ηBalance≤globalCap :=by
  have hrow:=hlocal.2.2.2.2.2.2.2.1
  have hcol:=hlocal.2.2.2.2.2.2.2.2
  have hterm:0≤etaLocal/rho:=div_nonneg hLocalEta hrho.le
  have heq:etaLocal+(ε*etaGlobal+etaLocal)/rho=
      (1+2/rho)*etaLocal+ε*etaGlobal/rho-etaLocal/rho:=by ring
  rw [heq]
  constructor <;> nlinarith
end Oberwolfach
