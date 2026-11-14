module

public import Oberwolfach.OrdinaryFreshPairEmbeddings

@[expose] public section

/-! Physical edge-disjointness and host containment of embedded finite
pairs, derived from their injective label maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V₁ U₁ V U:Type}
    [Fintype V₀] [Fintype U₀] [Fintype V₁] [Fintype U₁] [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V₁] [DecidableEq U₁] [DecidableEq V] [DecidableEq U]

theorem ordinary_resources_disjoint_of_rows (K L:Finset (Sym2 V⊕(V×U)))
    (h:Disjoint (ordinaryResourceRows K) (ordinaryResourceRows L)) : Disjoint K L := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      exact Finset.disjoint_left.mp h
        (show v∈ordinaryResourceRows K from Finset.mem_biUnion.mpr ⟨.inl s(v,w),he,by simp⟩)
        (show v∈ordinaryResourceRows L from Finset.mem_biUnion.mpr ⟨.inl s(v,w),he',by simp⟩)
  | inr p=>
    exact Finset.disjoint_left.mp h
      (show p.1∈ordinaryResourceRows K from Finset.mem_biUnion.mpr ⟨.inr p,he,by simp⟩)
      (show p.1∈ordinaryResourceRows L from Finset.mem_biUnion.mpr ⟨.inr p,he',by simp⟩)

theorem OrdinaryPairHostEmbedding.map_le {G₀:SimpleGraph V₀} {Hs:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop} (e:OrdinaryPairHostEmbedding G₀ Hs Q H) : G₀.map e.row≤Q := by
  intro v w h
  obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj _ _ _ _).mp h
  exact e.rim a b hab

theorem OrdinaryPairHostEmbedding.resources_disjoint {G₀:SimpleGraph V₀} {Hs:V₀→U₀→Prop}
    {G₁:SimpleGraph V₁} {Ht:V₁→U₁→Prop} {Q:SimpleGraph V} {H:V→U→Prop}
    (e:OrdinaryPairHostEmbedding G₀ Hs Q H) (e':OrdinaryPairHostEmbedding G₁ Ht Q H)
    (h:∀ a b,e.row a≠e'.row b) : Disjoint e.resources e'.resources := by
  apply ordinary_resources_disjoint_of_rows
  apply (show Disjoint (Finset.univ.image e.row) (Finset.univ.image e'.row) from ?_).mono e.resource_rows e'.resource_rows
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
  obtain ⟨b,hb,hba⟩:=Finset.mem_image.mp hv'
  exact h a b hba.symm

theorem OrdinaryPairHostEmbedding.row_card {G₀:SimpleGraph V₀} {Hs:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop} (e:OrdinaryPairHostEmbedding G₀ Hs Q H) :
    (Finset.univ.image e.row).card=Fintype.card V₀ := by
  rw [Finset.card_image_of_injective _ e.row.injective,Finset.card_univ]

theorem OrdinaryPairHostEmbedding.hub_card {G₀:SimpleGraph V₀} {Hs:V₀→U₀→Prop}
    {Q:SimpleGraph V} {H:V→U→Prop} (e:OrdinaryPairHostEmbedding G₀ Hs Q H) :
    (Finset.univ.image e.hub).card=Fintype.card U₀ := by
  rw [Finset.card_image_of_injective _ e.hub.injective,Finset.card_univ]

end Oberwolfach
