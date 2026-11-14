module

public import Oberwolfach.PrescribedPiecePositionsPhysical
public import Oberwolfach.PrescribedDependentInitialEdges

@[expose] public section
/-! A single source factor in the dependent family is the same ordered
path-and-cycle model as the one used for prescribed-position selection. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

def prescribedTaggedPieces (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):
    List (Unit×PrescribedSourcePiece (X i)) := (pieces i).map (fun p=>((),p))

theorem prescribed_tagged_graph (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):
    prescribedSourceGraph (prescribedTaggedPieces pieces i) ()=prescribedDependentGraph pieces i := by
  unfold prescribedSourceGraph prescribedDependentGraph
  congr 1
  ext e
  simp [prescribedSourcePhysical,prescribedDependentPhysical,prescribedTaggedPieces]

theorem prescribed_tagged_digraph (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):
    prescribedSourceDigraph (prescribedTaggedPieces pieces i) ()=prescribedDependentDigraph pieces i := by
  funext x y
  simp [prescribedSourceDigraph,prescribedDependentDigraph,prescribedTaggedPieces]

theorem prescribed_tagged_shape (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I)
    (hshape:∀ p∈pieces i,p.Shape):∀ p∈prescribedTaggedPieces pieces i,p.2.Shape := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  exact hshape q hq

theorem prescribed_tagged_apart (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I)
    (hapart:(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)):
    (prescribedTaggedPieces pieces i).Pairwise PrescribedPiecesApart := by
  unfold prescribedTaggedPieces
  rw [List.pairwise_map]
  apply hapart.imp
  intro p q h
  exact Or.inr h

theorem prescribed_dependent_positions (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I)
    (hshape:∀ p∈pieces i,p.Shape)
    (hapart:(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (A:Finset (X i)) (hA:∀x∈A,∀y∈A,¬(prescribedDependentGraph pieces i).Adj x y)
    (f:X i→V) (hinj:Set.InjOn f (↑A:Set (X i)))
    (M:Finset (V×V)) (hM:IsPrescribedOrientedMatching M) (Z:Finset V)
    (hOldM:Disjoint (A.image f) (prescribedMatchingEndpoints M))
    (hOldZ:Disjoint (A.image f) Z) (hMZ:Disjoint (prescribedMatchingEndpoints M) Z)
    (harc:Fintype.card (X i)≤(prescribedArcFinset (prescribedDependentDigraph pieces i)).card+A.card)
    (hsize:8*A.card+8*M.card+4*Z.card+10≤Fintype.card (X i)):
    ∃ (B:Finset (X i)) (g:X i→V),A⊆B ∧ Set.InjOn g (↑B:Set (X i)) ∧ (∀x∈A,g x=f x) ∧
      B.image g=A.image f∪prescribedMatchingEndpoints M∪Z ∧
      (prescribedInducedArcs (prescribedDependentDigraph pieces i) B).image (Prod.map g g)=M ∧
      (prescribedInducedSourceEdges (prescribedDependentGraph pieces i) B).image (Sym2.map g)=M.image prescribedArcPhysical := by
  have hh:=prescribed_piece_positions_physical (prescribedTaggedPieces pieces i)
    (prescribed_tagged_shape pieces i hshape) (prescribed_tagged_apart pieces i hapart) () A
    (by simpa only [prescribed_tagged_graph] using hA) f hinj M hM Z hOldM hOldZ hMZ
    (by simpa only [prescribed_tagged_digraph] using harc) hsize
  simpa only [prescribed_tagged_graph,prescribed_tagged_digraph] using hh
end Oberwolfach
