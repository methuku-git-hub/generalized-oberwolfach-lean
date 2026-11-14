module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! The three physical boundary graphs have the expected row neighbourhoods:
inside roots see outside labels and outside roots see the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_rim_neighbors
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (v:V):
    ((ordinaryBoundaryGraph Q H I J).comap Sum.inl).neighborFinset v=
      if v∈I then Q.neighborFinset v\I else Q.neighborFinset v∩I:=by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  change (ordinaryBoundaryGraph Q H I J).Adj (Sum.inl v) (Sum.inl w)↔_
  rw [ordinaryBoundaryGraph_adj]
  simp only [ordinaryInnerVertices_left]
  change Q.Adj v w ∧ ((v∉I ∧ w∈I) ∨ (w∉I ∧ v∈I)) ↔ _
  by_cases hv:v∈I <;> simp only [hv,ite_true,ite_false,Finset.mem_sdiff,Finset.mem_inter,
    SimpleGraph.mem_neighborFinset] <;> tauto

theorem ordinary_boundary_spoke_neighbors
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (v:V):
    (Finset.univ.filter (fun u=>(ordinaryBoundaryGraph Q H I J).Adj (Sum.inl v) (Sum.inr u)))=
      if v∈I then (Finset.univ.filter (H v))\J else J.filter (H v):=by
  ext u
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [ordinaryBoundaryGraph_adj]
  simp only [ordinaryInnerVertices_left,ordinaryInnerVertices_right]
  change H v u ∧ ((v∉I ∧ u∈J) ∨ (u∉J ∧ v∈I)) ↔ _
  by_cases hv:v∈I <;> simp only [hv,ite_true,ite_false,Finset.mem_sdiff,Finset.mem_filter,
    Finset.mem_univ,true_and] <;> tauto
end Oberwolfach
