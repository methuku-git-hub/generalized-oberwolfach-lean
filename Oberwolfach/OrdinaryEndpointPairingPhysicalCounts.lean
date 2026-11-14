module

public import Oberwolfach.OrdinaryEndpointPhysicalGeometry

@[expose] public section
/-! Exact cardinality identities between endpoint pairing neighborhoods
    in the physical graph and the underlying rim and spoke classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_pairing_physical_counts
    (Q:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (x:V):
    let S:Finset (V⊕U):=(A∩Q.neighborFinset x).image Sum.inl;
    let T:Finset (V⊕U):=(B.filter (H x)).image Sum.inr;
    let P:=ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B);
    (∀v∈A,((T∩P.neighborFinset (Sum.inl v)).card:ℝ)=
      ((B.filter (fun u=>H x u∧H v u)).card:ℝ)) ∧
    (∀u∈B,((S∩P.neighborFinset (Sum.inr u)).card:ℝ)=
      ((A.filter (fun v=>Q.Adj x v∧H v u)).card:ℝ)) ∧
    (∀v∈A,∀w∈A,(((T∩P.neighborFinset (Sum.inl v))∩P.neighborFinset (Sum.inl w)).card:ℝ)=
      ((B.filter (fun u=>H x u∧H v u∧H w u)).card:ℝ)):=by
  intro S T P
  constructor
  · intro v hv
    have he:T∩P.neighborFinset (Sum.inl v)=(B.filter (fun u=>H x u∧H v u)).image Sum.inr:=by
      ext z
      simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset]
      cases z <;> simp [T,P,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset,hv,and_assoc, and_left_comm, and_comm]
    rw [he,Finset.card_image_of_injective _ Sum.inr_injective]
  constructor
  · intro u hu
    have he:S∩P.neighborFinset (Sum.inr u)=(A.filter (fun v=>Q.Adj x v∧H v u)).image Sum.inl:=by
      ext z
      simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset]
      cases z <;> simp [S,P,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset,hu,and_assoc, and_left_comm, and_comm]
    rw [he,Finset.card_image_of_injective _ Sum.inl_injective]
  · intro v hv w hw
    have he:(T∩P.neighborFinset (Sum.inl v))∩P.neighborFinset (Sum.inl w)=
        (B.filter (fun u=>H x u∧H v u∧H w u)).image Sum.inr:=by
      ext z
      simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset]
      cases z <;> simp [T,P,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset,hv,hw,and_assoc, and_left_comm, and_comm]
    rw [he,Finset.card_image_of_injective _ Sum.inr_injective]
end Oberwolfach
