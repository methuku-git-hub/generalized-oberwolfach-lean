module

public import Oberwolfach.PrescribedAllVerticesEmbedding

@[expose] public section
/-! After padding by isolated singleton paths, free source occurrences are
exactly all pairs consisting of an index and an unprescribed source vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I:Type} [Fintype I] [DecidableEq I] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem prescribed_padded_free_vertices (pieces:∀i,List (PrescribedSourcePiece (X i))) (B:∀i,Finset (X i)):
    prescribedDependentFreeVertices (prescribedPadSingletons pieces) B=
      Finset.univ.filter (fun z:(Σi,X i)=>z.2∉B z.1) := by
  ext z
  simp [prescribedDependentFreeVertices,prescribed_padding_vertices]
end Oberwolfach
