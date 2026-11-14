module

public import Oberwolfach.MixedFreshParentDataInsideRoots
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The remaining hub and neighborhood inputs for the mixed factor, stated
separately from the endpoint weights constructed from the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryMixedOtherParentInputsInside (γ κ b B ε η:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (Z:Finset U) where
  hub_size:∀j:{u:U // u∉Z},κ*Fintype.card V≤((ordinaryBoundaryHubSet H Z A j).card:ℝ)
  rim_conflict:∀v,(F.degree v:ℝ)≤ε*Fintype.card V
  physical_conflict:∀w:V⊕U,((ordinaryPhysicalGraph F (fun _ _=>False)).degree w:ℝ)≤ε*Fintype.card (V⊕U)
  hub_neighborhoods:∀j:{u:U // u∉Z},∀Y:Finset V,Y⊆ordinaryBoundaryHubSet H Z A j→Y.card≤3→
    γ*Fintype.card V≤((common (ordinaryBoundaryHubSet H Z A j) Y
      (fun x=>(spanningRestriction Q A).neighborFinset x)).card:ℝ)
  endpoint_neighborhoods:∀i:{v:V // v∉A},EndpointNeighbourCounts
    (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
    (ordinaryPhysicalGraph F (fun _ _=>False))
    ((ordinaryBoundaryRimSet Q A i).image Sum.inl) ((ordinaryBoundaryRowSet H A Z i).image Sum.inr)
    (γ*Fintype.card (V⊕U))
  hub_weight:∀j:{u:U // u∉Z},LocalOrdinaryCycle (spanningRestriction Q A) F (ordinaryBoundaryHubSet H Z A j) 3→ℝ
  hub_weight_bounds:∀j C,b/(Fintype.card V:ℝ)^2≤hub_weight j C ∧ hub_weight j C≤B/(Fintype.card V:ℝ)^2
  hub_weight_load:∀j,∀v∈ordinaryBoundaryHubSet H Z A j,|1-hypergraphWeightedDegree localOrdinaryVertices (hub_weight j) v|≤η
end Oberwolfach
