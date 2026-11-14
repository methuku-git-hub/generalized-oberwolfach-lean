module

public import Oberwolfach.PrescribedPieceShape

@[expose] public section
/-! Relabelling ordered source pieces by an injection preserves their
vertices, physical edges, directed arcs and path/cycle shape. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y:Type} [DecidableEq X] [DecidableEq Y]

def PrescribedSourcePiece.map (f:X→Y):PrescribedSourcePiece X→PrescribedSourcePiece Y
  | .path xs=>.path (xs.map f)
  | .cycle a xs=>.cycle (f a) (xs.map f)

theorem prescribed_piece_map_vertices (f:X→Y) (p:PrescribedSourcePiece X):
    (p.map f).vertices=p.vertices.map f := by cases p <;> rfl

theorem prescribed_directed_path_edges_map (f:X→Y):
    ∀ xs:List X,prescribedDirectedPathEdges (xs.map f)=
      (prescribedDirectedPathEdges xs).image (Prod.map f f) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      simp only [List.map_cons,prescribedDirectedPathEdges,Finset.image_insert,Prod.map_apply]
      simp only [List.map_cons] at ih
      rw [ih]

theorem prescribed_ordered_path_edges_map (f:X→Y):
    ∀ xs:List X,prescribedOrderedPathEdges (xs.map f)=
      (prescribedOrderedPathEdges xs).image (Sym2.map f) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      simp only [List.map_cons,prescribedOrderedPathEdges,Finset.image_insert,Sym2.map_mk]
      simp only [List.map_cons] at ih
      rw [ih]

theorem prescribed_piece_map_arcs (f:X→Y) (p:PrescribedSourcePiece X):
    (p.map f).arcs=p.arcs.image (Prod.map f f) := by
  cases p with
  | path xs =>exact prescribed_directed_path_edges_map f xs
  | cycle a xs =>
    simpa [PrescribedSourcePiece.map,PrescribedSourcePiece.arcs,List.map_append] using
      prescribed_directed_path_edges_map f ((a::xs)++[a])

theorem prescribed_piece_map_edges (f:X→Y) (p:PrescribedSourcePiece X):
    (p.map f).edges=p.edges.image (Sym2.map f) := by
  cases p with
  | path xs =>exact prescribed_ordered_path_edges_map f xs
  | cycle a xs =>
    simpa [PrescribedSourcePiece.map,PrescribedSourcePiece.edges,List.map_append] using
      prescribed_ordered_path_edges_map f ((a::xs)++[a])

theorem prescribed_piece_map_shape (f:X→Y) (hf:Function.Injective f) (p:PrescribedSourcePiece X)
    (hp:p.Shape):(p.map f).Shape := by
  cases p with
  | path xs =>exact hp.map hf
  | cycle a xs =>
    constructor
    · exact hp.1.map hf
    · simpa using hp.2
end Oberwolfach
