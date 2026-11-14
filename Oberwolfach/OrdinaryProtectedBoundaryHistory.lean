module

public import Oberwolfach.OrdinaryProtectedEarlierLevels
public import Oberwolfach.OrdinaryBoundaryPhysicalDeletion

@[expose] public section
/-! Earlier protected levels do not change the later boundary, even in the
presence of a subsequent deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nested_protected_boundary_after_two_deletions
    (Q:SimpleGraph V) (H:V→U→Prop) (R:I→SimpleGraph V) (S:I→V→U→Prop)
    (E:SimpleGraph (V⊕U)) (X T:Finset V) (Z W:Finset U)
    (Told:I→Finset V) (Wold:I→Finset U)
    (hX:∀i,X⊆Told i) (hZ:∀i,Z⊆Wold i)
    (havoid:∀i,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (Told i) (Wold i))):
    let C:=⨆i,ordinaryPhysicalGraph (R i) (S i);
    spanningRestriction
      (ordinaryBoundaryGraph ((Q\C.comap Sum.inl)\E.comap Sum.inl)
        (ordinarySpokesAfterPhysicalDeletion (ordinarySpokesAfterPhysicalDeletion H C) E) T W)
      (ordinaryInnerVertices X Z)=
    spanningRestriction
      (ordinaryBoundaryGraph (Q\E.comap Sum.inl) (ordinarySpokesAfterPhysicalDeletion H E) T W)
      (ordinaryInnerVertices X Z):=by
  intro C
  rw [ordinary_boundary_graph_after_two_physical_deletions, ordinary_boundary_graph_after_physical_deletion]
  apply graph_spanning_after_two_deletions
  apply ordinary_protected_union_inner_zero
  intro i
  exact (havoid i).mono_right (ordinary_deep_blocker_mono X (Told i) Z (Wold i) (hX i) (hZ i))
end Oberwolfach
