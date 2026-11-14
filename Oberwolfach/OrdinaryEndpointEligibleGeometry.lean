module

public import Oberwolfach.OrdinaryEndpointPhysicalGeometry
public import Oberwolfach.EndpointMatchingMass

@[expose] public section
/-! The eligible parent graph on the physical sum is the original eligible
rim graph with an empty hub part. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_parent_neighbors (P:SimpleGraph V) (X:Finset V) (x:V):
    (X.image (Sum.inl:V→V⊕U))∩
      (ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x)=
    (X∩P.neighborFinset x).image Sum.inl:=by
  ext a
  cases a with
  | inl v=>simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
  | inr u=>simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]

theorem ordinary_endpoint_eligible_graph (P F:SimpleGraph V) (X:Finset V) (x:V):
    endpointEligibleGraph (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((X.image (Sum.inl:V→V⊕U))∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
      (Sum.inl x)=
    ordinaryPhysicalGraph (endpointEligibleGraph P F (X∩P.neighborFinset x) x) (fun _ _=>False):=by
  rw [ordinary_endpoint_parent_neighbors]
  ext a b
  cases a with
  | inl v=>cases b with
    | inl w=>simp [endpointEligibleGraph,ordinaryPhysicalGraph]
    | inr u=>simp [endpointEligibleGraph,ordinaryPhysicalGraph]
  | inr u=>cases b with
    | inl v=>simp [endpointEligibleGraph,ordinaryPhysicalGraph]
    | inr u'=>simp [endpointEligibleGraph,ordinaryPhysicalGraph]
end Oberwolfach
