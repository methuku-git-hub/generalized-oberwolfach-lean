module

public import Oberwolfach.MarkedReferenceLevelXiMonotonicity
public import Oberwolfach.MarkedReferenceLevelStepProperty

@[expose] public section
/-! The larger admissible size bound changes no graphs, domains, labels,
or deletion states used in the step conclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Gamma Color:Type} [Fintype Gamma] [Fintype Color]
variable {r d N NI Kgeom:ℕ}
variable {gamma rho omega t p0 betaA aLoA BA kappa ξ ξ' thetaDeep alphaInner omegaInner
  iota β aLo B η x omegaI hIcut deltaI etaBal:ℝ}

theorem marked_reference_step_from_larger_xi
    (level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA
      kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal)
    (hξ:ξ≤ξ') (gammaLoss sigmaLoss:ℝ)
    (h:MarkedReferenceLevelStepProperty (marked_reference_level_increase_xi level hξ) gammaLoss sigmaLoss):
    MarkedReferenceLevelStepProperty level gammaLoss sigmaLoss :=by
  simpa only [MarkedReferenceLevelStepProperty,marked_reference_level_increase_xi] using h
end Oberwolfach
