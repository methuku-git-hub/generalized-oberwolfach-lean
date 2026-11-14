module

public import Oberwolfach.OrdinaryEndpointEligibleGeometry
public import Oberwolfach.EndpointPotentialPredicates

@[expose] public section
/-! Translate the parent row and eligible-edge domains between the original
rim vertices and the physical sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_typed_parent_row_domain (P F:SimpleGraph V) (A:Finset V) (x:V):
    common (A.image (Sum.inl:V→V⊕U)) {Sum.inl x}
      (fun z=>((ordinaryPhysicalGraph P (fun _ _=>False))\
        (ordinaryPhysicalGraph F (fun _ _=>False))).neighborFinset z)=
    (common A {x} (fun z=>(P\F).neighborFinset z)).image Sum.inl:=by
  ext a
  cases a with
  | inl v=>simp [common,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]
  | inr u=>simp [common,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]

theorem endpoint_typed_parent_eligible_edge (P F:SimpleGraph V) (A:Finset V) (x:V) (e:Sym2 V):
    Sym2.map (Sum.inl:V→V⊕U) e∈(endpointEligibleGraph (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
      (Sum.inl x)).edgeSet ↔ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet:=by
  rw [ordinary_endpoint_eligible_graph]
  induction e using Sym2.ind with
  | _ v w=>simp [ordinaryPhysicalGraph,SimpleGraph.mem_edgeSet]
end Oberwolfach
