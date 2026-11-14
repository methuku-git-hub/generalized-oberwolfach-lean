module

public import Oberwolfach.OrdinaryProtectedDeletionHistory
public import Oberwolfach.OrdinaryProtectedBoundaryEdit

@[expose] public section
/-! All earlier protected deletions vanish in a nested pair; the actual
physical edit inside that pair costs at most the latest level's inner cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deletion_history_inner_edit
    (Q:SimpleGraph V) (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ)
    (X:Finset V) (Z:Finset U) (Told:ℕ→Finset V) (Wold:ℕ→Finset U) (cost:ℝ)
    (hX:∀i<n,X⊆Told i) (hZ:∀i<n,Z⊆Wold i)
    (havoid:∀i<n,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (Told i) (Wold i)))
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R n) (S n))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost):
    let G:=spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z);
    let G':=spanningRestriction (ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (n+1))
      (ordinaryHistorySpokes H R S (n+1))) (ordinaryInnerVertices X Z);
    ∀w:V⊕U,((changed (G.neighborFinset w) (G'.neighborFinset w)).card:ℝ)≤cost:=by
  intro G G'
  let D:=spanningRestriction (ordinaryPhysicalGraph (R n) (S n)) (ordinaryInnerVertices X Z)
  have hzero:=ordinary_deletion_history_inner_zero R S n X Z Told Wold hX hZ havoid
  have hphys:ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (n+1)) (ordinaryHistorySpokes H R S (n+1)) =
      (ordinaryPhysicalGraph Q H\ordinaryDeletionHistory R S n)\ordinaryPhysicalGraph (R n) (S n):=by
    rw [show ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (n+1)) (ordinaryHistorySpokes H R S (n+1)) =
      ordinaryPhysicalGraph (Q\(ordinaryDeletionHistory R S (n+1)).comap Sum.inl)
        (ordinarySpokesAfterPhysicalDeletion H (ordinaryDeletionHistory R S (n+1))) from rfl]
    rw [ordinary_physical_graph_after_deletion,ordinaryDeletionHistory]
    ext a b
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
    tauto
  have he:G'=G\D:=by
    have hh:=graph_spanning_after_two_deletions (ordinaryPhysicalGraph Q H) (ordinaryDeletionHistory R S n)
      (ordinaryPhysicalGraph (R n) (S n)) (ordinaryInnerVertices X Z) hzero
    have he':spanningRestriction (ordinaryPhysicalGraph Q H\ordinaryPhysicalGraph (R n) (S n))
      (ordinaryInnerVertices X Z)=G\D:=by
      ext a b
      simp only [G,D,spanningRestriction_adj,SimpleGraph.sdiff_adj]
      tauto
    change spanningRestriction (ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (n+1))
      (ordinaryHistorySpokes H R S (n+1))) (ordinaryInnerVertices X Z)=G\D
    rw [hphys,hh,he']
  intro w
  have hb:=graph_changed_neighbors_after_deletion G D w
  have hb':((changed (G.neighborFinset w) ((G\D).neighborFinset w)).card:ℝ)≤D.degree w:=by exact_mod_cast hb
  rw [he]
  convert hb'.trans (hcost w) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
