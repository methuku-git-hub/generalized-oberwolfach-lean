module

public import Oberwolfach.WalkDartUnions
public import Oberwolfach.FiniteSequenceWalkEdgeSet

@[expose] public section
/-! Forgetting the direction of physical walk arcs gives the physical edge set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem walk_physical_edges_eq_arc_image
    {V:Type*} [DecidableEq V] {G:SimpleGraph V} {a b:V} (p:G.Walk a b):
    walkPhysicalEdges p=(walkPhysicalArcs p).image (fun x:V×V=>({x.1,x.2}:Finset V)) := by
  ext e
  simp only [walkPhysicalEdges,walkPhysicalArcs,SimpleGraph.Walk.edges_eq_map_darts,
    List.map_map,List.mem_toFinset,List.mem_map,Finset.mem_image]
  constructor
  · rintro ⟨d,hd,he⟩
    refine ⟨d.toProd,⟨d,hd,rfl⟩,?_⟩
    simpa [SimpleGraph.Dart.edge,Sym2.toFinset_mk_eq] using he
  · rintro ⟨x,⟨d,hd,hx⟩,he⟩
    refine ⟨d,hd,?_⟩
    simpa [SimpleGraph.Dart.edge,Sym2.toFinset_mk_eq,←hx] using he

theorem walk_physical_arcs_disjoint_of_edges_disjoint
    {V:Type*} [DecidableEq V] {G:SimpleGraph V} {a b c d:V}
    (p:G.Walk a b) (q:G.Walk c d) (h:Disjoint (walkPhysicalEdges p) (walkPhysicalEdges q)):
    Disjoint (walkPhysicalArcs p) (walkPhysicalArcs q) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hp:({x.1,x.2}:Finset V)∈walkPhysicalEdges p:=by
    rw [walk_physical_edges_eq_arc_image]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hq:({x.1,x.2}:Finset V)∈walkPhysicalEdges q:=by
    rw [walk_physical_edges_eq_arc_image]
    exact Finset.mem_image.mpr ⟨x,hy,rfl⟩
  exact Finset.disjoint_left.mp h hp hq
end Oberwolfach
