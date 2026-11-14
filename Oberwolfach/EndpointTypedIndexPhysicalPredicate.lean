module

public import Oberwolfach.OrdinaryEndpointEligibleGeometry
public import Oberwolfach.EndpointPotentialPredicates

@[expose] public section
/-! The physical hub-root predicate agrees with the original two-domain
rim-edge predicate after the left embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_typed_index_physical_predicate (P R F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (x:V) (u:U) (e:Sym2 V):
    EndpointIndexPotentialPredicate (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph R (fun _ _=>False)) (ordinaryPhysicalGraph ⊥ H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl)
      (Sum.inl x) (Sum.inr u) (Sym2.map Sum.inl e) ↔
    e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet ∧
      e∈R.edgeSet ∧ ∀v∈e,R.Adj x v∧H v u:=by
  unfold EndpointIndexPotentialPredicate
  rw [ordinary_endpoint_eligible_graph]
  induction e using Sym2.ind with
  | _ v w=>simp [ordinaryPhysicalGraph,SimpleGraph.mem_edgeSet,Sym2.forall]
end Oberwolfach
