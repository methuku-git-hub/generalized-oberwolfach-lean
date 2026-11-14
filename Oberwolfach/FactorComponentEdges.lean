module

public import Oberwolfach.FactorWalkOrderedEdges

@[expose] public section
/-! Every edge incident with a cycle component is one of its walk edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_component_ordered_edges (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (v:V):
    ∃ p:F.Walk v v, p.IsCycle ∧ p.support.dropLast.Nodup ∧
      3≤p.support.dropLast.length ∧ p.support.dropLast++[v]=p.support ∧
      (∀ x,x∈p.support.dropLast ↔ x∈(F.connectedComponentMk v).supp) ∧
      (∀ x,x∈p.support.dropLast→∀ y,
        F.Adj x y ↔ s(x,y)∈prescribedOrderedPathEdges p.support) := by
  obtain ⟨p,hcycle,hnodup,hlen,hclosed,hvertices⟩:=two_factor_component_ordered_cycle F hF v
  refine ⟨p,hcycle,hnodup,hlen,hclosed,hvertices,?_⟩
  intro x hx y
  have hx' : x∈p.toSubgraph.verts := by
    rw [p.mem_verts_toSubgraph]
    exact List.mem_of_mem_dropLast hx
  have hadj := hcycle.adj_toSubgraph_iff_of_isCycles (two_factor_is_cycles F hF) hx' y
  rw [←walk_edges_eq_ordered_path_edges F p, List.mem_toFinset,
    ←SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact hadj.symm
end Oberwolfach
