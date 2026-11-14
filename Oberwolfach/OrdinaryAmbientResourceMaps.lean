module

public import Oberwolfach.OrdinaryGraphPairEmbeddings
public import Oberwolfach.TransformerOriginalEdgeIdentity

@[expose] public section

/-! Extend maps of finite row and hub sets to the ambient types. The
resource map commutes with the two embeddings, so edge-bijection proofs
for the finite graphs transfer without assuming vertex-map injectivity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V₁ U₁ V U : Type}
    [Fintype V₀] [Fintype U₀] [Fintype V₁] [Fintype U₁] [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V₁] [DecidableEq U₁] [DecidableEq V] [DecidableEq U]

def ordinaryPairResourceMap {A B C D : Type*} (f : A → C) (g : B → D) :
    (Sym2 A⊕(A×B)) → (Sym2 C⊕(C×D)) := Sum.map (Sym2.map f) (Prod.map f g)

def ordinaryAmbientMap {A B C : Type*} (i : A ↪ C) (j : B ↪ C) (f : A → B) : C → C :=
  Function.extend i (j∘f) id

@[simp] theorem ordinaryAmbientMap_apply {A B C : Type*} (i : A ↪ C) (j : B ↪ C) (f : A → B) (a : A) :
    ordinaryAmbientMap i j f (i a)=j (f a) := i.injective.extend_apply (j∘f) id a

theorem ordinaryAmbient_resource_commutes (i : V₀ ↪ V) (j : V₁ ↪ V) (s : U₀ ↪ U) (t : U₁ ↪ U)
    (f : V₀ → V₁) (g : U₀ → U₁) (e : Sym2 V₀⊕(V₀×U₀)) :
    ordinaryPairResourceMap (ordinaryAmbientMap i j f) (ordinaryAmbientMap s t g)
      (ordinaryPairResourceEmbedding i s e)=
      ordinaryPairResourceEmbedding j t (ordinaryPairResourceMap f g e) := by
  cases e with
  | inl e =>
    induction e using Sym2.ind with
    | _ a b =>
      change Sum.inl s(ordinaryAmbientMap i j f (i a),ordinaryAmbientMap i j f (i b))=
        Sum.inl s(j (f a),j (f b))
      rw [ordinaryAmbientMap_apply,ordinaryAmbientMap_apply]
  | inr p =>
    rcases p with ⟨a,b⟩
    change Sum.inr (ordinaryAmbientMap i j f (i a),ordinaryAmbientMap s t g (s b))=Sum.inr (j (f a),t (g b))
    rw [ordinaryAmbientMap_apply,ordinaryAmbientMap_apply]

theorem transformerImageResources_eq_image (G : SimpleGraph V) (H : V → U → Prop) (f : V → V) (g : U → U) :
    transformerImageResources G H f g=(ordinaryHostResources G H).image (ordinaryPairResourceMap f g) := by
  have hmap (a : Sym2 V) : Sym2.map f a=s(f a.out.1,f a.out.2) := by
    calc
      _ = Sym2.map f s(a.out.1,a.out.2) := congrArg (Sym2.map f) a.out_eq.symm
      _ = _ := rfl
  ext e
  simp only [transformerImageResources,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (⟨a,rfl⟩|⟨p,rfl⟩)
    · refine ⟨.inl a.val,(ordinaryHostResources_rim _ _ _).mpr ?_,?_⟩
      · simpa only [SimpleGraph.mem_edgeFinset] using a.property
      · exact congrArg Sum.inl (hmap a.val)
    · exact ⟨.inr p.val,(ordinaryHostResources_spoke _ _ _ _).mpr p.property,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    cases a with
    | inl a =>
      have hmem : a∈G.edgeFinset := by
        simpa only [SimpleGraph.mem_edgeFinset] using (ordinaryHostResources_rim _ _ _).mp ha
      refine Or.inl ⟨⟨a,hmem⟩,?_⟩
      exact congrArg Sum.inl (hmap a).symm
    | inr p =>
      exact Or.inr ⟨⟨p,(ordinaryHostResources_spoke _ _ _ _).mp ha⟩,rfl⟩

theorem ordinaryAmbient_resource_bijection
    (G₀ : SimpleGraph V₀) (H₀ : V₀ → U₀ → Prop) (G₁ : SimpleGraph V₁) (H₁ : V₁ → U₁ → Prop)
    (i : V₀ ↪ V) (j : V₁ ↪ V) (s : U₀ ↪ U) (t : U₁ ↪ U)
    (f : V₀ → V₁) (g : U₀ → U₁)
    (hinj : Set.InjOn (ordinaryPairResourceMap f g) (ordinaryHostResources G₀ H₀))
    (him : (ordinaryHostResources G₀ H₀).image (ordinaryPairResourceMap f g)=ordinaryHostResources G₁ H₁) :
    Set.InjOn (ordinaryPairResourceMap (ordinaryAmbientMap i j f) (ordinaryAmbientMap s t g))
      (ordinaryHostResources (G₀.map i) (ordinaryMappedSpokes H₀ i s)) ∧
      transformerImageResources (G₀.map i) (ordinaryMappedSpokes H₀ i s)
        (ordinaryAmbientMap i j f) (ordinaryAmbientMap s t g)=
        ordinaryHostResources (G₁.map j) (ordinaryMappedSpokes H₁ j t) := by
  constructor
  · rw [←ordinaryHostResources_embedding_image]
    intro a ha b hb he
    obtain ⟨a,ha₀,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb₀,rfl⟩ := Finset.mem_image.mp hb
    rw [ordinaryAmbient_resource_commutes,ordinaryAmbient_resource_commutes] at he
    exact congrArg (ordinaryPairResourceEmbedding i s)
      (hinj ha₀ hb₀ ((ordinaryPairResourceEmbedding j t).injective he))
  · rw [transformerImageResources_eq_image,←ordinaryHostResources_embedding_image,
      ←ordinaryHostResources_embedding_image,Finset.image_image]
    have hh : (ordinaryHostResources G₀ H₀).image
        (ordinaryPairResourceMap (ordinaryAmbientMap i j f) (ordinaryAmbientMap s t g) ∘ ordinaryPairResourceEmbedding i s)=
        ((ordinaryHostResources G₀ H₀).image (ordinaryPairResourceMap f g)).image (ordinaryPairResourceEmbedding j t) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro e _
      exact ordinaryAmbient_resource_commutes i j s t f g e
    rw [hh,him]

end Oberwolfach
