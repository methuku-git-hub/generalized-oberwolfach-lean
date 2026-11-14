module

public import Oberwolfach.ResidualSingleCyclePiecesWithArcs
public import Oberwolfach.ResidualPieceUnions

@[expose] public section
/-! Directed-arc unions respect concatenation of source-piece lists. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem source_piece_arcs_union_append (ps qs:List (PrescribedSourcePiece V)):
    sourcePieceArcsUnion (ps++qs)=sourcePieceArcsUnion ps∪sourcePieceArcsUnion qs := by
  simp [sourcePieceArcsUnion,Finset.union_biUnion]
end Oberwolfach
