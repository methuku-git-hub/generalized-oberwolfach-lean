module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic

@[expose] public section
/-! Two explicitly listed triangles have disjoint edges but intersect in a
vertex. Matching on cycle edge-sets therefore does not by itself imply a
vertex-disjoint cycle packing. -/
set_option autoImplicit false
namespace Oberwolfach

def exampleLeftTriangleVertices : Finset (Fin 5) := {0,1,2}
def exampleRightTriangleVertices : Finset (Fin 5) := {0,3,4}
def exampleLeftTriangleEdges : Finset (Finset (Fin 5)) := {{0,1},{1,2},{0,2}}
def exampleRightTriangleEdges : Finset (Finset (Fin 5)) := {{0,3},{3,4},{0,4}}

theorem edge_disjoint_triangles_can_share_a_vertex:
    Disjoint exampleLeftTriangleEdges exampleRightTriangleEdges ∧
    ¬Disjoint exampleLeftTriangleVertices exampleRightTriangleVertices ∧
    (0:Fin 5)∈exampleLeftTriangleVertices ∧ (0:Fin 5)∈exampleRightTriangleVertices:=by
  decide
end Oberwolfach
