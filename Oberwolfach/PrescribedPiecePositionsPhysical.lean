module

public import Oberwolfach.PrescribedPiecePositions
public import Oberwolfach.PrescribedDirectedPhysicalImage

@[expose] public section
/-! The selected directed matching and the embedding theorem's initial
physical edge set agree exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_piece_positions_physical (ps:List (I×PrescribedSourcePiece X))
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
      (prescribedInducedArcs (prescribedSourceDigraph ps i) B).image (Prod.map g g)=M ∧
      (prescribedInducedSourceEdges (prescribedSourceGraph ps i) B).image (Sym2.map g)=M.image prescribedArcPhysical := by
  obtain ⟨B,g,hAB,hinj',hext,himage,harcs⟩:=prescribed_piece_positions ps hshape hapart i A hA f hinj M hM Z hOldM hOldZ hMZ harc hsize
  refine ⟨B,g,hAB,hinj',hext,himage,harcs,?_⟩
  rw [prescribed_induced_physical_image (prescribedSourceGraph ps i) (prescribedSourceDigraph ps i)
    (prescribed_source_model_representation ps i) (prescribed_source_model_arc_graph ps hshape i) B g,harcs]
end Oberwolfach
