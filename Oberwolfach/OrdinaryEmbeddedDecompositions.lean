module

public import Oberwolfach.OrdinaryGraphPairEmbeddings
public import Oberwolfach.ResourceEmbeddingDecompositions
public import Oberwolfach.OrdinaryAttachmentAssembly

@[expose] public section

/-! Transport exact ordinary wheel decompositions to the actual embedded
finite graphs. In particular the attachment remainder has a decomposition
after embedding, rather than merely an abstract edge-count identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U' : Type*} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
    [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_decomposition_embedding (G : SimpleGraph V) (H : V → U → Prop) (r : ℕ)
    (φ : V ↪ V') (ψ : U ↪ U') (h : HasOrdinaryWheelDecomposition G H r) :
    HasOrdinaryWheelDecomposition (G.map φ) (ordinaryMappedSpokes H φ ψ) r := by
  unfold HasOrdinaryWheelDecomposition
  rw [←ordinaryHostResources_embedding_image]
  exact resource_decomposition_embedding ordinaryWheelResources ordinaryWheelResources
    (ordinaryPairResourceEmbedding φ ψ) (universalOrdinaryWheelEmbedding φ ψ)
    (ordinaryPairResourceEmbedding φ ψ).injective (universalOrdinaryWheelEmbedding_resources φ ψ)
    (ordinaryHostResources G H) h

end Oberwolfach
