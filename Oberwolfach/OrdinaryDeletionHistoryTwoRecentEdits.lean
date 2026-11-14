module

public import Oberwolfach.OrdinaryProtectedDeletionHistoryInnerEdit
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! If the earlier deletions avoid a target but the two most recent ones may
meet it, their two local costs bound the total edit inside that target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deletion_history_two_recent_edits
    (Q:SimpleGraph V) (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (i:ℕ) (hi:0 < i)
    (X:Finset V) (Z:Finset U) (Told:ℕ→Finset V) (Wold:ℕ→Finset U) (costPrev costNow:ℝ)
    (hX:∀j, j+1 < i → X⊆Told j) (hZ:∀j, j+1 < i → Z⊆Wold j)
    (havoid:∀j, j+1 < i → Disjoint (ordinaryPhysicalGraph (R j) (S j)) (ordinaryDeepBlocker (Told j) (Wold j)))
    (hprev:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R (i-1)) (S (i-1)))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤costPrev)
    (hnow:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R i) (S i))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤costNow):
    let B:=spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)
    let B':=spanningRestriction (ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (i+1))
      (ordinaryHistorySpokes H R S (i+1))) (ordinaryInnerVertices X Z);
    ∀w:V⊕U,((changed (B.neighborFinset w) (B'.neighborFinset w)).card:ℝ)≤costPrev+costNow:=by
  intro B B' w
  let Bpre:=spanningRestriction (ordinaryPhysicalGraph (ordinaryHistoryRim Q R S i)
    (ordinaryHistorySpokes H R S i)) (ordinaryInnerVertices X Z)
  let D:=spanningRestriction (ordinaryPhysicalGraph (R i) (S i)) (ordinaryInnerVertices X Z)
  have hearlier:=ordinary_deletion_history_inner_edit Q H R S (i-1) X Z Told Wold costPrev
    (fun j hj=>hX j (by omega)) (fun j hj=>hZ j (by omega))
    (fun j hj=>havoid j (by omega)) hprev w
  have hearlier':((changed (B.neighborFinset w) (Bpre.neighborFinset w)).card:ℝ)≤costPrev:=by
    rw [show i-1+1=i by omega] at hearlier
    convert hearlier using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hphys:ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (i+1)) (ordinaryHistorySpokes H R S (i+1)) =
      (ordinaryPhysicalGraph Q H\ordinaryDeletionHistory R S i)\ordinaryPhysicalGraph (R i) (S i):=by
    rw [show ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (i+1)) (ordinaryHistorySpokes H R S (i+1)) =
      ordinaryPhysicalGraph (Q\(ordinaryDeletionHistory R S (i+1)).comap Sum.inl)
        (ordinarySpokesAfterPhysicalDeletion H (ordinaryDeletionHistory R S (i+1))) from rfl]
    rw [ordinary_physical_graph_after_deletion,ordinaryDeletionHistory]
    ext a b
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
    tauto
  have hpre:ordinaryPhysicalGraph (ordinaryHistoryRim Q R S i) (ordinaryHistorySpokes H R S i) =
      ordinaryPhysicalGraph Q H\ordinaryDeletionHistory R S i:=by
    exact ordinary_physical_graph_after_deletion Q H (ordinaryDeletionHistory R S i)
  have hpost:B'=Bpre\D:=by
    change spanningRestriction (ordinaryPhysicalGraph (ordinaryHistoryRim Q R S (i+1))
      (ordinaryHistorySpokes H R S (i+1))) (ordinaryInnerVertices X Z)=Bpre\D
    rw [hphys,←hpre]
    ext a b
    simp only [Bpre,D,spanningRestriction_adj,SimpleGraph.sdiff_adj]
    tauto
  have hlast:=graph_changed_neighbors_after_deletion Bpre D w
  have hlast':((changed (Bpre.neighborFinset w) (B'.neighborFinset w)).card:ℝ)≤costNow:=by
    rw [hpost]
    have hh:((changed (Bpre.neighborFinset w) ((Bpre\D).neighborFinset w)).card:ℝ)≤D.degree w:=by
      exact_mod_cast hlast
    convert hh.trans (hnow w) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have htriangle:((changed (B.neighborFinset w) (B'.neighborFinset w)).card:ℝ)≤
      ((changed (B.neighborFinset w) (Bpre.neighborFinset w)).card:ℝ)+
      ((changed (Bpre.neighborFinset w) (B'.neighborFinset w)).card:ℝ):=by
    exact_mod_cast changed_card_triangle (B.neighborFinset w) (Bpre.neighborFinset w) (B'.neighborFinset w)
  linarith
end Oberwolfach
