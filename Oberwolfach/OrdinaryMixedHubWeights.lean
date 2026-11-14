module

public import Oberwolfach.OrdinaryMixedOtherParentInputsInside

@[expose] public section
/-! The remaining weighted hub-cycle input, isolated from the neighborhood
and conflict conditions proved from the common sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryMixedHubWeights (b B η:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (Z:Finset U) where
  weight:∀j:{u:U // u∉Z},LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) 3→ℝ
  bounds:∀j C,b/(Fintype.card V:ℝ)^2≤weight j C ∧ weight j C≤B/(Fintype.card V:ℝ)^2
  loads:∀j,∀v∈ordinaryBoundaryHubSet H Z A j,|1-hypergraphWeightedDegree localOrdinaryVertices (weight j) v|≤η
end Oberwolfach
