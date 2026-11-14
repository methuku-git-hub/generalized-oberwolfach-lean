module

public import Oberwolfach.PrescribedEmbeddingDisjointUpdate
public import Oberwolfach.Definitions

@[expose] public section
/-! A new physical edge set avoiding the full forbidden graph preserves
cross-factor disjointness and avoids the separately reserved graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem prescribed_embedding_physical_step (E:I→Finset (Sym2 V)) (k:I)
    (added:Finset (Sym2 V)) (F J:SimpleGraph V)
    (hpair:PairwisePhysicalDisjoint E) (hcover:∀ j,E j⊆F.edgeFinset)
    (hJ:J.edgeFinset⊆F.edgeFinset) (havoid:Disjoint added F.edgeFinset):
    PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧
      Disjoint added J.edgeFinset := by
  constructor
  · apply prescribed_embedding_disjoint_update E k added hpair
    intro j hj
    exact havoid.mono_right (hcover j)
  · exact havoid.mono_right hJ
end Oberwolfach
