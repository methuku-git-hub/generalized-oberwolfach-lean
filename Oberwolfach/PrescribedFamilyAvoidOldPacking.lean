module

public import Oberwolfach.PrescribedAvoidOldPacking

@[expose] public section
/-! This application retains the original physical packing while completing
all separately typed prescribed factors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

theorem prescribed_dependent_source_representation (pieces:∀ i,List (PrescribedSourcePiece (X i))) (i:I):
    ∀x y,(prescribedDependentGraph pieces i).Adj x y→
      prescribedDependentDigraph pieces i x y ∨ prescribedDependentDigraph pieces i y x := by
  rw [←prescribed_tagged_graph pieces i,←prescribed_tagged_digraph pieces i]
  exact prescribed_source_model_representation (prescribedTaggedPieces pieces i) ()

theorem prescribed_family_avoids_old_packing
    (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (B:∀ i,Finset (X i)) (g Φ:∀ i,X i→V)
    (hold:∀i x,x∈B i→Φ i x=g i x) (M:I→Finset (V×V))
    (hM:∀i,(prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image (Prod.map (g i) (g i))=M i)
    (D:V→V→Prop) (harc:∀i x y,prescribedDependentDigraph pieces i x y→(x∉B i ∨ y∉B i)→D (Φ i x) (Φ i y))
    (K:Finset (Sym2 V)) (hMavoid:∀i,Disjoint ((M i).image prescribedArcPhysical) K)
    (hDavoid:∀x y,D x y→s(x,y)∉K):
    ∀i,Disjoint (((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))) K := by
  intro i
  exact prescribed_embedding_avoids_physical_packing (prescribedDependentGraph pieces i) (prescribedDependentDigraph pieces i)
    (prescribed_dependent_source_representation pieces i) (B i) (g i) (Φ i) (hold i) (M i) (hM i) D (harc i) K (hMavoid i) hDavoid
end Oberwolfach
