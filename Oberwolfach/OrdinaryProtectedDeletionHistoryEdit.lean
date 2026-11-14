module

public import Oberwolfach.OrdinaryProtectedDeletionHistory

@[expose] public section
/-! The boundary in the actual sequentially deleted host is changed by at
most the most recent level's boundary cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deletion_history_boundary_edit
    (Q:SimpleGraph V) (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ)
    (X T:Finset V) (Z W:Finset U) (Told:ℕ→Finset V) (Wold:ℕ→Finset U) (cost:ℝ)
    (hX:∀i<n,X⊆Told i) (hZ:∀i<n,Z⊆Wold i)
    (havoid:∀i<n,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (Told i) (Wold i)))
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (R n) (S n) T W)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost):
    let G:=spanningRestriction (ordinaryBoundaryGraph Q H T W) (ordinaryInnerVertices X Z);
    let G':=spanningRestriction (ordinaryBoundaryGraph (ordinaryHistoryRim Q R S (n+1))
      (ordinaryHistorySpokes H R S (n+1)) T W) (ordinaryInnerVertices X Z);
    ∀w:V⊕U,((changed (G.neighborFinset w) (G'.neighborFinset w)).card:ℝ)≤cost:=by
  intro G G'
  have hzero:=ordinary_deletion_history_inner_zero R S n X Z Told Wold hX hZ havoid
  have hkeep:G'=spanningRestriction (ordinaryBoundaryGraph (Q\R n) (fun v u=>H v u∧¬S n v u) T W)
      (ordinaryInnerVertices X Z):=by
    rw [show G'=spanningRestriction (ordinaryBoundaryGraph (ordinaryHistoryRim Q R S (n+1))
      (ordinaryHistorySpokes H R S (n+1)) T W) (ordinaryInnerVertices X Z) from rfl]
    rw [ordinary_history_rim_step,ordinary_history_spokes_step]
    have hh:=graph_spanning_after_two_deletions (ordinaryBoundaryGraph Q H T W) (ordinaryDeletionHistory R S n)
      (ordinaryPhysicalGraph (R n) (S n)) (ordinaryInnerVertices X Z) hzero
    rw [←ordinary_boundary_graph_after_two_physical_deletions,←ordinary_boundary_graph_after_physical_deletion] at hh
    convert hh using 1 <;> rfl
  intro w
  have hb:=ordinary_protected_boundary_edit Q (R n) H (S n) X T Z W cost hcost w
  rw [hkeep]
  convert hb using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
