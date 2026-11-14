module

public import Oberwolfach.OrdinaryEndpointEligibleGeometry
public import Oberwolfach.EndpointMatchingTargets
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! Parent row targets and eligible-edge masses are unchanged when the rim
vertices are embedded in the physical sum. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem endpoint_typed_physical_row_target (P F:SimpleGraph V) (A:Finset V) (x v:V)
    (weight:Sym2 (V⊕U)→ℝ):
    endpointEligibleRowWeight (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
      (Sum.inl x) (Sum.inl v) (fun a b=>weight s(a,b))=
    endpointEligibleRowWeight F (A∩P.neighborFinset x) x v
      (fun a b=>weight s(Sum.inl a,Sum.inl b)):=by
  rw [ordinary_endpoint_parent_neighbors]
  unfold endpointEligibleRowWeight
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    simp [ordinaryPhysicalGraph]
  · intro a ha b hb hab
    exact Sum.inl.inj hab

theorem endpoint_typed_physical_edge_mass (P F:SimpleGraph V) (A:Finset V) (x:V)
    (weight:Sym2 (V⊕U)→ℝ):
    (∑e∈(endpointEligibleGraph (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A.image Sum.inl)∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
      (Sum.inl x)).edgeFinset,weight e)=
    ∑e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight (Sym2.map Sum.inl e):=by
  rw [ordinary_endpoint_eligible_graph,←graph_map_inl_physical]
  let E:=endpointEligibleGraph P F (A∩P.neighborFinset x) x
  let f:V↪V⊕U:=Function.Embedding.inl
  have ht:(∑e∈(E.map f).edgeFinset,weight e)=
      ∑e∈E.edgeFinset,weight (Sym2.map Sum.inl e):=by
    rw [SimpleGraph.edgeFinset_map,Finset.sum_map]
    rfl
  convert ht using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
