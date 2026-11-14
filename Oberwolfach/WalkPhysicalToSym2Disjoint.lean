module

public import Oberwolfach.FiniteSequenceWalkEdgeSet

@[expose] public section
/-! Disjoint physical edge sets of two walks imply disjointness of their
symmetric edge lists. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem walk_sym2_edges_disjoint_of_physical
    {V:Type*} [DecidableEq V] {G H:SimpleGraph V} {a b c d:V}
    (p:G.Walk a b) (q:H.Walk c d)
    (hdis:Disjoint (walkPhysicalEdges p) (walkPhysicalEdges q)):
    Disjoint p.edges.toFinset q.edges.toFinset:=by
  classical
  apply Finset.disjoint_left.mpr
  intro e hep heq
  have hp:e.toFinset∈walkPhysicalEdges p:=by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨e,List.mem_toFinset.mp hep,rfl⟩
  have hq:e.toFinset∈walkPhysicalEdges q:=by
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨e,List.mem_toFinset.mp heq,rfl⟩
  exact Finset.disjoint_left.mp hdis hp hq
end Oberwolfach
