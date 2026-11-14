module

public import Oberwolfach.ResidualInternalNeighbors

@[expose] public section
/-! Edges incident with deleted vertices are exactly among the deleted cycle
and path edges, so the two residual domains define a graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I J:Type} [Fintype V] [DecidableEq V] [DecidableEq I] [DecidableEq J]

theorem two_factor_cycle_vertex_edges (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) {v:V} (p:F.Walk v v) (hp:p.IsCycle)
    (x y:V) (hx:x∈p.support.toFinset) (hxy:F.Adj x y):
    s(x,y)∈p.edges.toFinset := by
  have hx':x∈p.toSubgraph.verts := p.mem_verts_toSubgraph.mpr (List.mem_toFinset.mp hx)
  have hh:=hp.adj_toSubgraph_iff_of_isCycles (two_factor_is_cycles F hF) hx' y
  exact List.mem_toFinset.mpr (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp (hh.mpr hxy))

theorem two_factor_deleted_vertex_incident (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2)
    (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hp:∀i∈s,(P i).IsPath)
    (t:Finset J) (root:J→V) (C:∀ j,F.Walk (root j) (root j))
    (hc:∀j∈t,(C j).IsCycle)
    (x y:V) (hxy:F.Adj x y)
    (hx:x∈(t.biUnion (fun j=>(C j).support.toFinset)) ∪
       (s.biUnion (fun i=>(P i).support.toFinset \ {u i,v i}))):
    s(x,y)∈(t.biUnion (fun j=>(C j).edges.toFinset)) ∪
       (s.biUnion (fun i=>(P i).edges.toFinset)) := by
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨j,hj,hj'⟩:=Finset.mem_biUnion.mp hx
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨j,hj,two_factor_cycle_vertex_edges F hF (C j) (hc j hj) x y hj' hxy⟩
  · obtain ⟨i,hi,hi'⟩:=Finset.mem_biUnion.mp hx
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨i,hi,two_factor_internal_path_edges F hF (P i) (hp i hi) x y hi' hxy⟩
end Oberwolfach
