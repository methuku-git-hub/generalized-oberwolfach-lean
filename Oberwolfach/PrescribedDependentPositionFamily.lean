module

public import Oberwolfach.PrescribedDependentPositions

@[expose] public section
/-! Choose all prescribed matching positions simultaneously for separately
typed factors. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

theorem prescribed_dependent_position_family (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (hshape:∀ i p,p∈pieces i→p.Shape)
    (hapart:∀ i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (A:∀ i,Finset (X i)) (hA:∀ i x,x∈A i→∀ y,y∈A i→¬(prescribedDependentGraph pieces i).Adj x y)
    (f:∀ i,X i→V) (hinj:∀ i,Set.InjOn (f i) (↑(A i):Set (X i)))
    (M:I→Finset (V×V)) (hM:∀ i,IsPrescribedOrientedMatching (M i)) (Z:I→Finset V)
    (hOldM:∀ i,Disjoint ((A i).image (f i)) (prescribedMatchingEndpoints (M i)))
    (hOldZ:∀ i,Disjoint ((A i).image (f i)) (Z i))
    (hMZ:∀ i,Disjoint (prescribedMatchingEndpoints (M i)) (Z i))
    (harc:∀ i,Fintype.card (X i)≤(prescribedArcFinset (prescribedDependentDigraph pieces i)).card+(A i).card)
    (hsize:∀ i,8*(A i).card+8*(M i).card+4*(Z i).card+10≤Fintype.card (X i)):
    ∃ (B:∀ i,Finset (X i)) (g:∀ i,X i→V),∀ i,
      A i⊆B i ∧ Set.InjOn (g i) (↑(B i):Set (X i)) ∧ (∀x∈A i,g i x=f i x) ∧
      (B i).image (g i)=(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i ∧
      (prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image (Prod.map (g i) (g i))=M i ∧
      prescribedDependentInitialEdges pieces B g i=(M i).image prescribedArcPhysical := by
  have hh:∀ i,∃ (B:Finset (X i)) (g:X i→V),A i⊆B ∧ Set.InjOn g (↑B:Set (X i)) ∧ (∀x∈A i,g x=f i x) ∧
      B.image g=(A i).image (f i)∪prescribedMatchingEndpoints (M i)∪Z i ∧
      (prescribedInducedArcs (prescribedDependentDigraph pieces i) B).image (Prod.map g g)=M i ∧
      (prescribedInducedSourceEdges (prescribedDependentGraph pieces i) B).image (Sym2.map g)=(M i).image prescribedArcPhysical := by
    intro i
    exact prescribed_dependent_positions pieces i (hshape i) (hapart i) (A i) (hA i) (f i) (hinj i)
      (M i) (hM i) (Z i) (hOldM i) (hOldZ i) (hMZ i) (harc i) (hsize i)
  choose B g hB using hh
  exact ⟨B,g,fun i=>hB i⟩
end Oberwolfach
