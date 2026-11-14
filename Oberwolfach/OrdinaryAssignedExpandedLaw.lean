module

public import Oberwolfach.OrdinaryAssignedInnerEndpointLawInputs

@[expose] public section
/-! Name the exact assigned expanded law so independent event selectors can
be combined without unfolding the dependent sampling construction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryAssignedExpandedLaw
    {n q D K:ℕ} (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e) :=
  let p:=initialIndexDensity (Fin q) D*rsv/2
  let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
  let qMark:=ordinaryAssignedMarkedProbability F hF K θ c
  let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
  FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
    sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd
    qMark sampling.hq sampling.hQ s sampling.hs sampling.hS)
end Oberwolfach
