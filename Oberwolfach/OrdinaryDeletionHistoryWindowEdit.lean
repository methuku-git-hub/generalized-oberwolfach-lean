module

public import Oberwolfach.OrdinaryDeletionHistoryWindowDegree
public import Oberwolfach.OrdinaryProtectedBoundaryEdit

@[expose] public section
/-! A finite window of unprotected recent deletions gives a quantitative
    edit bound on the actual inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deletion_history_inner_window_edit
    (Q:SimpleGraph V) (H:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop) (n:ℕ)
    (X:Finset V) (Z:Finset U) (J:Finset ℕ) (cost:ℕ→ℝ)
    (hzero:∀j<n,j∉J→spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices X Z)=⊥)
    (hcost:∀j∈J,∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤cost j):
    let G:=spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z);
    let G':=spanningRestriction (ordinaryPhysicalGraph (ordinaryHistoryRim Q R S n)
      (ordinaryHistorySpokes H R S n)) (ordinaryInnerVertices X Z);
    ∀w:V⊕U,((changed (G.neighborFinset w) (G'.neighborFinset w)).card:ℝ)≤∑j∈J,cost j :=by
  intro G G'
  let D:=spanningRestriction (ordinaryDeletionHistory R S n) (ordinaryInnerVertices X Z)
  have he:G'=G\D:=by
    change spanningRestriction (ordinaryPhysicalGraph (Q\(ordinaryDeletionHistory R S n).comap Sum.inl)
      (ordinarySpokesAfterPhysicalDeletion H (ordinaryDeletionHistory R S n))) (ordinaryInnerVertices X Z)=G\D
    rw [ordinary_physical_graph_after_deletion]
    ext a b
    simp only [G,D,spanningRestriction_adj,SimpleGraph.sdiff_adj]
    tauto
  have hD:=ordinary_deletion_history_inner_window_degree R S n X Z J cost hzero hcost
  intro w
  have hb:=graph_changed_neighbors_after_deletion G D w
  have hb':((changed (G.neighborFinset w) ((G\D).neighborFinset w)).card:ℝ)≤D.degree w:=by exact_mod_cast hb
  rw [he]
  convert hb'.trans (hD w) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
