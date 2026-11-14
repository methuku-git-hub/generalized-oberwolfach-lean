module

public import Oberwolfach.OrdinaryAttachmentHostDecomposition
public import Oberwolfach.OrdinaryAttachmentAssembly
public import Oberwolfach.OrdinaryGraphPairEmbeddings

@[expose] public section

/-! Exact attachment identities after embedding. The original pair,
extra wheels and full attachment are compared as actual physical edge sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U I W:Type}
    [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype I] [Fintype W]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq W]

theorem ordinaryOldPair_embedding (G:SimpleGraph V₀) (H:V₀→U₀→Prop)
    (φ:V₀↪V) (ψ:U₀↪U) (f:V₀⊕(I×W)↪V) (g:U₀⊕I↪U)
    (hf:∀ a,f (.inl a)=φ a) (hg:∀ b,g (.inl b)=ψ b) :
    ((ordinaryOldRim G).map f=G.map φ) ∧
    ordinaryMappedSpokes (ordinaryOldSpokes H) f g=ordinaryMappedSpokes H φ ψ := by
  constructor
  · rw [ordinaryOldRim,SimpleGraph.map_map]
    congr 1
    funext a
    exact hf a
  · funext a b
    apply propext
    constructor
    · rintro ⟨x,y,h,hx,hy⟩
      cases x with
      | inr x=>exact h.elim
      | inl x=>
        cases y with
        | inr y=>exact h.elim
        | inl y=>exact ⟨x,y,h,(hf x).symm.trans hx,(hg y).symm.trans hy⟩
    · rintro ⟨x,y,h,hx,hy⟩
      exact ⟨.inl x,.inl y,h,(hf x).trans hx,(hg y).trans hy⟩

theorem ordinary_embedded_attachment_resources (G:SimpleGraph V₀) (H:V₀→U₀→Prop)
    (C:SimpleGraph W) (z:W) (ρ:I→V₀)
    (φ:V₀↪V) (ψ:U₀↪U) (f:V₀⊕(I×W)↪V) (g:U₀⊕I↪U)
    (hf:∀ a,f (.inl a)=φ a) (hg:∀ b,g (.inl b)=ψ b) :
    let old:=ordinaryHostResources (G.map φ) (ordinaryMappedSpokes H φ ψ)
    let extra:=ordinaryHostResources ((ordinaryAttachmentRim ⊥ C z ρ).map f)
      (ordinaryMappedSpokes (ordinaryAttachmentSpokes (fun (_:V₀) (_:U₀)=>False) z ρ) f g)
    let full:=ordinaryHostResources ((ordinaryAttachmentRim G C z ρ).map f)
      (ordinaryMappedSpokes (ordinaryAttachmentSpokes H z ρ) f g)
    full=old∪extra ∧ Disjoint old extra := by
  dsimp only
  obtain ⟨hr,hs⟩:=ordinaryOldPair_embedding G H φ ψ f g hf hg
  have he:ordinaryHostResources ((ordinaryOldRim G).map f) (ordinaryMappedSpokes (ordinaryOldSpokes H) f g)=
      ordinaryHostResources (G.map φ) (ordinaryMappedSpokes H φ ψ):=by rw [hr,hs]
  constructor
  · rw [←ordinaryHostResources_embedding_image,ordinaryAttachment_resources_union,Finset.image_union,
      ordinaryHostResources_embedding_image,ordinaryHostResources_embedding_image,he]
  · have hh:Disjoint
        ((ordinaryHostResources (ordinaryOldRim G) (ordinaryOldSpokes H)).image (ordinaryPairResourceEmbedding f g))
        ((ordinaryHostResources (ordinaryAttachmentRim ⊥ C z ρ)
          (ordinaryAttachmentSpokes (fun (_:V₀) (_:U₀)=>False) z ρ)).image (ordinaryPairResourceEmbedding f g)):=
      by
        apply Finset.disjoint_left.mpr
        intro e he he'
        obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
        obtain ⟨b,hb,heq⟩:=Finset.mem_image.mp he'
        have hab: b=a := (ordinaryPairResourceEmbedding f g).injective heq
        subst b
        exact Finset.disjoint_left.mp (ordinaryAttachment_resources_disjoint G H C z ρ) ha hb
    rwa [ordinaryHostResources_embedding_image,ordinaryHostResources_embedding_image,he] at hh

theorem ordinary_embedded_attachment_decomposition (Q F:SimpleGraph V) (H:V→U→Prop)
    (G₀:SimpleGraph V₀) (H₀:V₀→U₀→Prop) (C:SimpleGraph W) (r:ℕ)
    (hC:IsEmbeddedCycle C r) (hfull:∀ w,w∈C.support) (z:W) (ρ:I→V₀)
    (φ:V₀↪V) (ψ:U₀↪U) (f:V₀⊕(I×W)↪V) (g:U₀⊕I↪U)
    (hf:∀ a,f (.inl a)=φ a) (hg:∀ b,g (.inl b)=ψ b)
    (hQ:∀ a b,(ordinaryAttachmentRim ⊥ C z ρ).Adj a b→Q.Adj (f a) (f b))
    (hH:∀ a b,ordinaryAttachmentSpokes (fun (_:V₀) (_:U₀)=>False) z ρ a b→H (f a) (g b))
    (hcross:∀ i w a,¬F.Adj (f (.inr (i,w))) (f (.inl a)))
    (hnew:∀ i j w w',¬F.Adj (f (.inr (i,w))) (f (.inr (j,w'))))
    (hdec:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (G₀.map φ) (ordinaryMappedSpokes H₀ φ ψ))) :
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources ((ordinaryAttachmentRim G₀ C z ρ).map f)
        (ordinaryMappedSpokes (ordinaryAttachmentSpokes H₀ z ρ) f g)) := by
  obtain ⟨he,hd⟩:=ordinary_embedded_attachment_resources G₀ H₀ C z ρ φ ψ f g hf hg
  rw [he]
  exact resource_decomposition_union _ _ _ hdec
    (ordinary_attachment_extra_host_decomposition Q F H C hC hfull z ρ f g hQ hH hcross hnew) hd

end Oberwolfach
