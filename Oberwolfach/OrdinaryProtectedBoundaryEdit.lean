module

public import Oberwolfach.OrdinaryBoundaryPhysicalDeletion
public import Oberwolfach.OrdinaryDeepBlocker
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! The deep-boundary cost of one protected level bounds the actual
change of the next boundary inside the enclosing pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_changed_neighbors_after_deletion {W:Type} [Fintype W] [DecidableEq W]
    (G D:SimpleGraph W) (w:W):
    (changed (G.neighborFinset w) ((G\D).neighborFinset w)).card≤D.degree w:=by
  have hsub:changed (G.neighborFinset w) ((G\D).neighborFinset w)⊆D.neighborFinset w:=by
    intro v hv
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,
      SimpleGraph.sdiff_adj] at hv ⊢
    tauto
  have hh:=Finset.card_le_card hsub
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh

variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_boundary_edit
    (Q R:SimpleGraph V) (H S:V→U→Prop) (X T:Finset V) (Z W:Finset U) (deepCost:ℝ)
    (hcost:∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph R S T W)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤deepCost):
    let G:=spanningRestriction (ordinaryBoundaryGraph Q H T W) (ordinaryInnerVertices X Z);
    let G':=spanningRestriction (ordinaryBoundaryGraph (Q\R) (fun v u=>H v u∧¬S v u) T W)
      (ordinaryInnerVertices X Z);
    ∀w:V⊕U,((changed (G.neighborFinset w) (G'.neighborFinset w)).card:ℝ)≤deepCost:=by
  intro G G'
  let D:=spanningRestriction (ordinaryBoundaryGraph R S T W) (ordinaryInnerVertices X Z)
  have he:G'=G\D:=by
    ext a b
    simp only [G,G',D,spanningRestriction_adj,ordinaryBoundaryGraph_adj,SimpleGraph.sdiff_adj]
    cases a <;> cases b <;> simp only [ordinaryPhysicalGraph,SimpleGraph.sdiff_adj] <;> tauto
  intro w
  rw [he]
  have hh:=graph_changed_neighbors_after_deletion G D w
  have hh':((changed (G.neighborFinset w) ((G\D).neighborFinset w)).card:ℝ)≤D.degree w:=by
    exact_mod_cast hh
  convert hh'.trans (hcost w) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
