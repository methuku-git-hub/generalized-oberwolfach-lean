module

public import Oberwolfach.PrescribedSourcePieces

@[expose] public section
/-! The undirected edges of a source piece are exactly the physical images of
its directed arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

def prescribedArcPhysical (e:X×X):Sym2 X:=s(e.1,e.2)

theorem prescribed_ordered_edges_are_arc_images:
    ∀ xs:List X,prescribedOrderedPathEdges xs=(prescribedDirectedPathEdges xs).image prescribedArcPhysical := by
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      simp only [prescribedOrderedPathEdges,prescribedDirectedPathEdges,Finset.image_insert,prescribedArcPhysical]
      rw [ih]

theorem prescribed_piece_edges_are_arc_images (p:PrescribedSourcePiece X):
    p.edges=p.arcs.image prescribedArcPhysical := by
  cases p with
  | path xs =>exact prescribed_ordered_edges_are_arc_images xs
  | cycle a xs =>exact prescribed_ordered_edges_are_arc_images ((a::xs)++[a])
end Oberwolfach
