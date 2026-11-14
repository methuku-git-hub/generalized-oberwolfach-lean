module

public import Oberwolfach.MarkedOrdinaryResourceLoads
public import Oberwolfach.OrderedOrdinarySpokeStability

@[expose] public section
/-! The ordinary part of the common marked resource state is exactly its
ordinary rim state and its retained ordinary-spoke state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_marked_state_pullback
    (R:(V×V)⊕(V×V)→Prop) (H:Bool→V→U→Prop):
    (fun a=>typedMarkedResourceState R H (ordinaryMarkedResourceEmbedding a))=
      (fun a=>decide (ordinaryPotentialKeep (fun xy=>R (Sum.inl xy)) (H false) a)) := by
  funext a
  cases a with
  | inl xy=>simp [typedMarkedResourceState,ordinaryMarkedResourceEmbedding,
      orderedOrdinaryResourceEmbedding,ordinaryPotentialKeep]
  | inr vu=>simp [typedMarkedResourceState,ordinaryMarkedResourceEmbedding,
      orderedOrdinaryResourceEmbedding,ordinaryPotentialKeep]
end Oberwolfach
