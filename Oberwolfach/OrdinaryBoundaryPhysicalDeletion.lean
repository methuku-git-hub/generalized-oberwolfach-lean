module

public import Oberwolfach.OrdinaryPhysicalGraphDeletion

@[expose] public section
/-! Physical-edge deletion commutes with restriction to the ordinary
boundary, so the factor classes are those of the actual leftover graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_graph_after_physical_deletion
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (K:SimpleGraph (V⊕U)):
    ordinaryBoundaryGraph (Q\K.comap Sum.inl) (ordinarySpokesAfterPhysicalDeletion H K) X Z =
      ordinaryBoundaryGraph Q H X Z\K:=by
  ext a b
  rw [ordinaryBoundaryGraph_adj,SimpleGraph.sdiff_adj,ordinaryBoundaryGraph_adj]
  have he:=ordinary_physical_graph_after_deletion Q H K
  have hadj:(ordinaryPhysicalGraph (Q\K.comap Sum.inl) (ordinarySpokesAfterPhysicalDeletion H K)).Adj a b ↔
      (ordinaryPhysicalGraph Q H\K).Adj a b:=by rw [he]
  rw [hadj]
  simp only [SimpleGraph.sdiff_adj]
  tauto

theorem ordinary_boundary_graph_after_two_physical_deletions
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (C D:SimpleGraph (V⊕U)):
    ordinaryBoundaryGraph ((Q\C.comap Sum.inl)\D.comap Sum.inl)
      (ordinarySpokesAfterPhysicalDeletion (ordinarySpokesAfterPhysicalDeletion H C) D) X Z =
      (ordinaryBoundaryGraph Q H X Z\C)\D:=by
  rw [ordinary_boundary_graph_after_physical_deletion,ordinary_boundary_graph_after_physical_deletion]
end Oberwolfach
