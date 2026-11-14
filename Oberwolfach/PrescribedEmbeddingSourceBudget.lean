module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! An injective partial embedding and its unembedded component use disjoint
parts of the actual source factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_embedding_assigned_and_unembedded_budget
    {X V:Type} [DecidableEq X] [DecidableEq V]
    (Q A C:Finset X) (φ:X→V) (hAC:Disjoint A C)
    (hsub:A∪C⊆Q) (hinj:Set.InjOn φ A):
    (A.image φ).card+C.card≤Q.card := by
  rw [Finset.card_image_of_injOn hinj,←Finset.card_union_of_disjoint hAC]
  exact Finset.card_le_card hsub
end Oberwolfach
