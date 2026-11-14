module

public import Oberwolfach.OrdinaryTrianglePrescribedJointProbability

@[expose] public section
/-! The three original raw-sample tests for the triangle cover, keeping the
small prescribed-edge load separate from geometric and edit scales. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

def OrdinaryTriangleSeparatedCoverEvent
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d Dmax:ℕ) (J:Finset U)
    (a p γ ρhub pR pH η θ ρ:ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop :=
  OrdinaryPrescribedInnerEvent 3 P F π d a p γ Finset.univ Finset.univ j σ ∧
  OrdinaryHubCoverEvent 2 P F π d ρhub j σ ∧
  OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ
    (Finset.univ\J) pR pH η θ ρ j σ
end Oberwolfach
