module

public import Oberwolfach.ResidualSingleCyclePieces

@[expose] public section
/-! Vertex and edge unions respect concatenation of source-piece lists. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem source_piece_vertices_union_append (ps qs:List (PrescribedSourcePiece V)):
    sourcePieceVerticesUnion (ps++qs)=sourcePieceVerticesUnion ps∪sourcePieceVerticesUnion qs := by
  simp [sourcePieceVerticesUnion,Finset.union_biUnion]

theorem source_piece_edges_union_append (ps qs:List (PrescribedSourcePiece V)):
    sourcePieceEdgesUnion (ps++qs)=sourcePieceEdgesUnion ps∪sourcePieceEdgesUnion qs := by
  simp [sourcePieceEdgesUnion,Finset.union_biUnion]

theorem source_piece_vertex_mem_union (ps:List (PrescribedSourcePiece V)) (p:PrescribedSourcePiece V)
    (hp:p∈ps) (x:V) (hx:x∈p.vertices):x∈sourcePieceVerticesUnion ps := by
  exact Finset.mem_biUnion.mpr ⟨p,List.mem_toFinset.mpr hp,List.mem_toFinset.mpr hx⟩
end Oberwolfach
