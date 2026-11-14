module

public import Oberwolfach.PrescribedPieceSourceOrientation
public import Oberwolfach.PrescribedArcCount

@[expose] public section
/-! The prescribed-position construction for the manuscript's ordered
path-and-cycle source model, with the structural conditions proved. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_piece_positions (ps:List (I×PrescribedSourcePiece X))
    (hshape:∀ p∈ps,p.2.Shape) (hapart:ps.Pairwise PrescribedPiecesApart) (i:I)
    (A:Finset X) (hA:∀x∈A,∀y∈A,¬(prescribedSourceGraph ps i).Adj x y)
    (f:X→V) (hinj:Set.InjOn f (↑A:Set X))
    (M:Finset (V×V)) (hM:IsPrescribedOrientedMatching M) (Z:Finset V)
    (hOldM:Disjoint (A.image f) (prescribedMatchingEndpoints M))
    (hOldZ:Disjoint (A.image f) Z) (hMZ:Disjoint (prescribedMatchingEndpoints M) Z)
    (harc:Fintype.card X≤(prescribedArcFinset (prescribedSourceDigraph ps i)).card+A.card)
    (hsize:8*A.card+8*M.card+4*Z.card+10≤Fintype.card X):
    ∃ (B:Finset X) (g:X→V),A⊆B ∧ Set.InjOn g (↑B:Set X) ∧ (∀x∈A,g x=f x) ∧
      B.image g=A.image f∪prescribedMatchingEndpoints M∪Z ∧
      (prescribedInducedArcs (prescribedSourceDigraph ps i) B).image (Prod.map g g)=M := by
  exact prescribed_positions_with_arc_count (prescribedSourceGraph ps i) (prescribedSourceDigraph ps i)
    (prescribed_source_model_degree ps hshape hapart i)
    (prescribed_source_model_representation ps i)
    (prescribed_source_model_arc_graph ps hshape i)
    (prescribed_source_model_oriented ps hshape hapart i)
    A hA f hinj M hM Z hOldM hOldZ hMZ harc hsize
end Oberwolfach
