module

public import Oberwolfach.OrdinaryWheelHostRecovery
public import Oberwolfach.OrdinaryGraphPairEmbeddings
public import Oberwolfach.ResourceEmbeddingDecompositions
public import Oberwolfach.OrdinaryAttachmentWheels

@[expose] public section

/-! The attached private wheels give a decomposition in the actual host,
including its forbidden-pair condition. Old roots need not be separated
from each other, because an attachment wheel contains at most one old root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U I W : Type}
    [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype I] [Fintype W]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq W]
    {r : ℕ}

theorem attachment_embedded_cycle_separated (F : SimpleGraph V) (z : W) (ρ : I → V₀)
    (f : V₀⊕(I×W) ↪ V)
    (hcross : ∀ i w a,¬F.Adj (f (.inr (i,w))) (f (.inl a)))
    (hnew : ∀ i j w w',¬F.Adj (f (.inr (i,w))) (f (.inr (j,w'))))
    (i : I) (w w' : W) :
    ¬F.Adj (f (attachmentWheelEmbedding z ρ i w)) (f (attachmentWheelEmbedding z ρ i w')) := by
  have he (a : W) : attachmentWheelEmbedding z ρ i a=
      if a=z then Sum.inl (ρ i) else Sum.inr (i,a) := by
    by_cases ha : a=z
    · rw [if_pos ha]
      exact (attachmentWheelEmbedding_old z ρ i a (ρ i)).mpr ⟨ha,rfl⟩
    · rw [if_neg ha]
      exact (attachmentWheelEmbedding_private z ρ i i a a).mpr ⟨ha,rfl,rfl⟩
  rw [he,he]
  by_cases hw : w=z <;> by_cases hw' : w'=z
  · simp only [hw,hw',ite_true];exact fun h=>h.ne rfl
  · simp only [hw,hw',ite_true,ite_false]
    exact fun h=>hcross i w' (ρ i) h.symm
  · simp only [hw,hw',ite_true,ite_false];exact hcross i w (ρ i)
  · simp only [hw,hw',ite_false];exact hnew i i w w'

theorem ordinary_attachment_extra_host_decomposition
    (Q F : SimpleGraph V) (H : V → U → Prop) (C : SimpleGraph W)
    (hC : IsEmbeddedCycle C r) (hfull : ∀ w,w∈C.support) (z : W) (ρ : I → V₀)
    (f : V₀⊕(I×W) ↪ V) (g : U₀⊕I ↪ U)
    (hQ : ∀ a b,(ordinaryAttachmentRim ⊥ C z ρ).Adj a b → Q.Adj (f a) (f b))
    (hH : ∀ a b,ordinaryAttachmentSpokes (fun (_ : V₀) (_ : U₀)=>False) z ρ a b → H (f a) (g b))
    (hcross : ∀ i w a,¬F.Adj (f (.inr (i,w))) (f (.inl a)))
    (hnew : ∀ i j w w',¬F.Adj (f (.inr (i,w))) (f (.inr (j,w')))) :
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources ((ordinaryAttachmentRim ⊥ C z ρ).map f)
        (ordinaryMappedSpokes (ordinaryAttachmentSpokes (fun (_ : V₀) (_ : U₀)=>False) z ρ) f g)) := by
  let W₀ := finiteAttachmentWheel (U:=U₀) C hC z ρ
  let W₁ := fun i=>universalOrdinaryWheelEmbedding f g (ordinaryWheelUniversal (W₀ i))
  have hWi (i : I) : ordinaryWheelResources (W₁ i)⊆ordinaryHostResources Q H := by
    apply (ordinaryWheelResources_subset_host _ Q H).mpr
    constructor
    · intro x y hxy
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj f _ _ _).mp hxy
      exact hQ a b ((W₀ i).val.1.property hab)
    · intro x hx
      change x∈((ordinaryWheelRim (W₀ i)).map f).support at hx
      rw [SimpleGraph.support_map] at hx
      obtain ⟨a,ha,rfl⟩ := hx
      exact hH a (.inr i) ((W₀ i).property.1 a ha)
  have hFi (i : I) : ∀ x∈(ordinaryWheelRim (W₁ i)).support,
      ∀ y∈(ordinaryWheelRim (W₁ i)).support,¬F.Adj x y := by
    intro x hx y hy
    change x∈((C.map (attachmentWheelEmbedding z ρ i)).map f).support at hx
    change y∈((C.map (attachmentWheelEmbedding z ρ i)).map f).support at hy
    rw [SimpleGraph.support_map] at hx hy
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    rw [SimpleGraph.support_map] at ha hb
    obtain ⟨w,_,rfl⟩ := ha
    obtain ⟨w',_,rfl⟩ := hb
    exact attachment_embedded_cycle_separated F z ρ f hcross hnew i w w'
  let W₂ := fun i=>ordinaryWheelInHost Q F H (W₁ i) (hWi i) (hFi i)
  rw [←ordinaryHostResources_embedding_image]
  apply resource_decomposition_embedding (fun i=>ordinaryWheelResources (W₀ i))
    ordinaryWheelResources (ordinaryPairResourceEmbedding f g) W₂ (ordinaryPairResourceEmbedding f g).injective
    (fun i=>universalOrdinaryWheelEmbedding_resources f g (ordinaryWheelUniversal (W₀ i)))
  refine ⟨Finset.univ,(fun i _ j _ hij=>finiteAttachmentWheels_disjoint C hC z ρ i j hij),?_⟩
  rw [←wheelFamily_resources W₀]
  rw [finiteAttachmentWheel_family_rim,finiteAttachmentWheel_family_spokes C hC z ρ hfull]

end Oberwolfach
