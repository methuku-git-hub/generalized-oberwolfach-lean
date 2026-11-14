module

public import Oberwolfach.MarkedWheelVertexEmbedding

@[expose] public section

/-! Composing nested vertex and hub embeddings composes their physical
resource maps exactly, including the finite set representing a rim edge. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedResourceEmbedding_comp_apply
    {V₀ V₁ V₂ U₀ U₁ U₂:Type} [DecidableEq V₀] [DecidableEq V₁] [DecidableEq V₂]
    [DecidableEq U₀] [DecidableEq U₁] [DecidableEq U₂]
    (f₁:V₁↪V₀) (f₂:V₂↪V₁) (g₁:U₁↪U₀) (g₂:U₂↪U₁)
    (z:Finset V₂⊕(V₂×U₂)):
    markedResourceEmbedding f₁ g₁ (markedResourceEmbedding f₂ g₂ z)=
      markedResourceEmbedding (f₂.trans f₁) (g₂.trans g₁) z:=by
  cases z with
  | inl a => simp [markedResourceEmbedding,Finset.image_image,Function.comp_def]
  | inr a => cases a;simp [markedResourceEmbedding]

end Oberwolfach
