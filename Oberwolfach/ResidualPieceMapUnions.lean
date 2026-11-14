module

public import Oberwolfach.ResidualPieceListSubtypeLift

@[expose] public section
/-! Relabelling source pieces commutes with their vertex, edge and arc unions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem source_piece_map_vertices_union (f:X→Y) (ps:List (PrescribedSourcePiece X)):
    sourcePieceVerticesUnion (ps.map (fun p=>p.map f))=(sourcePieceVerticesUnion ps).image f := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hp)
    rw [prescribed_piece_map_vertices] at hx
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hx)
    exact Finset.mem_image.mpr ⟨y,Finset.mem_biUnion.mpr ⟨q,List.mem_toFinset.mpr hq,List.mem_toFinset.mpr hy⟩,rfl⟩
  · intro hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨q,hq,hy⟩:=Finset.mem_biUnion.mp hy
    refine Finset.mem_biUnion.mpr ⟨q.map f,List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,List.mem_toFinset.mp hq,rfl⟩),?_⟩
    rw [prescribed_piece_map_vertices]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨y,List.mem_toFinset.mp hy,rfl⟩)

theorem source_piece_map_edges_union (f:X→Y) (ps:List (PrescribedSourcePiece X)):
    sourcePieceEdgesUnion (ps.map (fun p=>p.map f))=(sourcePieceEdgesUnion ps).image (Sym2.map f) := by
  ext e
  constructor
  · intro he
    obtain ⟨p,hp,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hp)
    rw [prescribed_piece_map_edges] at he
    obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨d,Finset.mem_biUnion.mpr ⟨q,List.mem_toFinset.mpr hq,hd⟩,rfl⟩
  · intro he
    obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨q,hq,hd⟩:=Finset.mem_biUnion.mp hd
    refine Finset.mem_biUnion.mpr ⟨q.map f,List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,List.mem_toFinset.mp hq,rfl⟩),?_⟩
    rw [prescribed_piece_map_edges]
    exact Finset.mem_image.mpr ⟨d,hd,rfl⟩

theorem source_piece_map_arcs_union (f:X→Y) (ps:List (PrescribedSourcePiece X)):
    sourcePieceArcsUnion (ps.map (fun p=>p.map f))=(sourcePieceArcsUnion ps).image (Prod.map f f) := by
  ext e
  constructor
  · intro he
    obtain ⟨p,hp,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hp)
    rw [prescribed_piece_map_arcs] at he
    obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨d,Finset.mem_biUnion.mpr ⟨q,List.mem_toFinset.mpr hq,hd⟩,rfl⟩
  · intro he
    obtain ⟨d,hd,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨q,hq,hd⟩:=Finset.mem_biUnion.mp hd
    refine Finset.mem_biUnion.mpr ⟨q.map f,List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,List.mem_toFinset.mp hq,rfl⟩),?_⟩
    rw [prescribed_piece_map_arcs]
    exact Finset.mem_image.mpr ⟨d,hd,rfl⟩
end Oberwolfach
