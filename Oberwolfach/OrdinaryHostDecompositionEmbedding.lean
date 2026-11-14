module

public import Oberwolfach.OrdinaryWheelHostRecovery
public import Oberwolfach.OrdinaryGraphPairEmbeddings
public import Oberwolfach.ResourceEmbeddingDecompositions

@[expose] public section
/-! Lift an exact wheel decomposition through injective vertex and hub maps,
keeping physical disjointness and the forbidden-pair condition in the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U V' U':Type} [Fintype V] [Fintype U] [Fintype V'] [Fintype U']
  [DecidableEq V] [DecidableEq U] [DecidableEq V'] [DecidableEq U']

theorem ordinary_host_decomposition_embedding
    (Q F K:SimpleGraph V) (H E:V→U→Prop)
    (Q' F':SimpleGraph V') (H':V'→U'→Prop) (r:ℕ)
    (φ:V↪V') (ψ:U↪U')
    (hQ:∀v w,Q.Adj v w→Q'.Adj (φ v) (φ w))
    (hH:∀v u,H v u→H' (φ v) (ψ u))
    (hF:∀v w,F'.Adj (φ v) (φ w)→F.Adj v w)
    (hdec:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources K E)):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q') (F:=F') (Hbase:=H') (r:=r))
      (ordinaryHostResources (K.map φ) (ordinaryMappedSpokes E φ ψ)):=by
  let W₁:=fun W:OrdinaryWheel Q F H r=>universalOrdinaryWheelEmbedding φ ψ (ordinaryWheelUniversal W)
  have hWi (W:OrdinaryWheel Q F H r):ordinaryWheelResources (W₁ W)⊆ordinaryHostResources Q' H':=by
    apply (ordinaryWheelResources_subset_host _ Q' H').mpr
    constructor
    · intro x y hxy
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj φ _ _ _).mp hxy
      exact hQ a b (W.val.1.property hab)
    · intro x hx
      change x∈((ordinaryWheelRim W).map φ).support at hx
      rw [SimpleGraph.support_map] at hx
      obtain ⟨a,ha,rfl⟩ := hx
      exact hH a (ordinaryWheelHub W) (W.property.1 a ha)
  have hFi (W:OrdinaryWheel Q F H r):∀x∈(ordinaryWheelRim (W₁ W)).support,
      ∀y∈(ordinaryWheelRim (W₁ W)).support,¬F'.Adj x y:=by
    intro x hx y hy hxy
    change x∈((ordinaryWheelRim W).map φ).support at hx
    change y∈((ordinaryWheelRim W).map φ).support at hy
    rw [SimpleGraph.support_map] at hx hy
    obtain ⟨a,ha,rfl⟩:=hx
    obtain ⟨b,hb,rfl⟩:=hy
    exact W.property.2 a ha b hb (hF a b hxy)
  let W₂:=fun W:OrdinaryWheel Q F H r=>ordinaryWheelInHost Q' F' H' (W₁ W) (hWi W) (hFi W)
  rw [←ordinaryHostResources_embedding_image]
  apply resource_decomposition_embedding ordinaryWheelResources ordinaryWheelResources
    (ordinaryPairResourceEmbedding φ ψ) W₂ (ordinaryPairResourceEmbedding φ ψ).injective ?_ (ordinaryHostResources K E) hdec
  intro W
  exact universalOrdinaryWheelEmbedding_resources φ ψ (ordinaryWheelUniversal W)
end Oberwolfach
