module

public import Oberwolfach.OrdinaryWheelInEmbeddedDomains

@[expose] public section
/-! Pull back a finite packing through the same two domain embeddings. The
physical resources, including cross-packing disjointness, are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]
  (φ:V↪W) (ψ:U↪Z) (G F:SimpleGraph V) (F':SimpleGraph W) (H:V→U→Prop) (r:ℕ)
  (hF:∀v w,F.Adj v w→F'.Adj (φ v) (φ w))

def ordinaryEmbeddedWheelPullback
    (T:OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r):OrdinaryWheel G F H r:=
  Classical.choose (ordinary_wheel_in_embedded_domains φ ψ G F F' H r hF T)

theorem ordinaryEmbeddedWheelPullback_resources
    (T:OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r):
    (ordinaryWheelResources (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF T)).image
      (ordinaryPairResourceEmbedding φ ψ)=ordinaryWheelResources T:=
  (Classical.choose_spec (ordinary_wheel_in_embedded_domains φ ψ G F F' H r hF T)).2.2


theorem ordinaryEmbeddedWheelPullback_rim
    (T:OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r):
    (ordinaryWheelRim (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF T)).map φ=ordinaryWheelRim T:=
  (Classical.choose_spec (ordinary_wheel_in_embedded_domains φ ψ G F F' H r hF T)).1

theorem ordinaryEmbeddedWheelPullback_hub
    (T:OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r):
    ψ (ordinaryWheelHub (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF T))=ordinaryWheelHub T:=
  (Classical.choose_spec (ordinary_wheel_in_embedded_domains φ ψ G F F' H r hF T)).2.1

theorem ordinaryEmbeddedWheelPullback_injective:
    Function.Injective (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF):=by
  intro A B he
  apply ordinaryWheelResources_injective
  rw [←ordinaryEmbeddedWheelPullback_resources φ ψ G F F' H r hF A,
    ←ordinaryEmbeddedWheelPullback_resources φ ψ G F F' H r hF B,he]

theorem ordinary_embedded_packing_resources
    (M:Finset (OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r)):
    ((M.image (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF)).biUnion ordinaryWheelResources).image
      (ordinaryPairResourceEmbedding φ ψ)=M.biUnion ordinaryWheelResources:=by
  ext x
  simp only [Finset.mem_image,Finset.mem_biUnion]
  constructor
  · rintro ⟨a,⟨S,⟨T,hT,rfl⟩,ha⟩,rfl⟩
    refine ⟨T,hT,?_⟩
    rw [←ordinaryEmbeddedWheelPullback_resources φ ψ G F F' H r hF T]
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  · rintro ⟨T,hT,hx⟩
    rw [←ordinaryEmbeddedWheelPullback_resources φ ψ G F F' H r hF T] at hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    exact ⟨a,⟨_,⟨T,hT,rfl⟩,ha⟩,rfl⟩

theorem ordinary_embedded_packings_disjoint
    (M N:Finset (OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r))
    (hdis:Disjoint (M.biUnion ordinaryWheelResources) (N.biUnion ordinaryWheelResources)):
    Disjoint ((M.image (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF)).biUnion ordinaryWheelResources)
      ((N.image (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF)).biUnion ordinaryWheelResources):=by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  have hm:(ordinaryPairResourceEmbedding φ ψ) a∈M.biUnion ordinaryWheelResources:=by
    rw [←ordinary_embedded_packing_resources φ ψ G F F' H r hF M]
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hn:(ordinaryPairResourceEmbedding φ ψ) a∈N.biUnion ordinaryWheelResources:=by
    rw [←ordinary_embedded_packing_resources φ ψ G F F' H r hF N]
    exact Finset.mem_image.mpr ⟨a,hb,rfl⟩
  exact Finset.disjoint_left.mp hdis hm hn
end Oberwolfach
