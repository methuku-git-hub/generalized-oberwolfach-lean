module

public import Oberwolfach.ResidualSpokeCardinality

@[expose] public section
/-! Canonical tail and head embeddings for a source permutation and an
injective embedding of the complement of the strict path interiors. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def complementTailDomain {X:Type*} [Fintype X] [DecidableEq X] (A B:Finset X):Finset X :=
  (Finset.univ\A)∪B

def complementTailEmbedding {X V:Type*} [Fintype X] [DecidableEq X]
    (A D B:Finset X) (hDA:D⊆A) (hBD:Disjoint B D) (fC:{x // x∉D}↪V):
    {x // x∈complementTailDomain A B}↪V where
  toFun x:=fC ⟨x.val,by
    intro hx
    rcases Finset.mem_union.mp x.property with hout | hb
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hx)
    · exact Finset.disjoint_left.mp hBD hb hx⟩
  inj':=by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z:{x // x∉D}=>z.val) (fC.injective h)

def complementHeadEmbedding {X V:Type*} [Fintype X] [DecidableEq X]
    (A D B T:Finset X) (hDA:D⊆A) (hTD:Disjoint T D)
    (σ:Equiv.Perm X) (hσ:(complementTailDomain A B).image σ=complementTailDomain A T)
    (fC:{x // x∉D}↪V):{x // x∈complementTailDomain A B}↪V where
  toFun x:=fC ⟨σ x.val,by
    have hx:σ x.val∈complementTailDomain A T:=by
      rw [←hσ]
      exact Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩
    intro hd
    rcases Finset.mem_union.mp hx with hout | ht
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hd)
    · exact Finset.disjoint_left.mp hTD ht hd⟩
  inj':=by
    intro x y h
    apply Subtype.ext
    apply σ.injective
    exact congrArg (fun z:{x // x∉D}=>z.val) (fC.injective h)

theorem complement_oriented_arc_images
    {X V:Type*} [Fintype X] [DecidableEq X] [DecidableEq V]
    (A D B T:Finset X) (hDA:D⊆A) (hBD:Disjoint B D) (hTD:Disjoint T D)
    (σ:Equiv.Perm X) (hσ:(complementTailDomain A B).image σ=complementTailDomain A T)
    (fC:{x // x∉D}↪V):
    (Finset.univ.image (complementTailEmbedding A D B hDA hBD fC)=
      Finset.univ.image ((complementDomainEmbedding hDA).trans fC) ∪
        Finset.univ.image ((endpointDomainEmbedding hBD).trans fC)) ∧
    (Finset.univ.image (complementHeadEmbedding A D B T hDA hTD σ hσ fC)=
      Finset.univ.image ((complementDomainEmbedding hDA).trans fC) ∪
        Finset.univ.image ((endpointDomainEmbedding hTD).trans fC)):=by
  classical
  constructor
  · ext v
    constructor
    · intro hv
      obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hv
      rcases Finset.mem_union.mp x.property with hout | hb
      · apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨⟨x.val,(Finset.mem_sdiff.mp hout).2⟩,Finset.mem_univ _,?_⟩
        exact hx
      · apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨⟨x.val,hb⟩,Finset.mem_univ _,?_⟩
        exact hx
    · intro hv
      rcases Finset.mem_union.mp hv with hz | hb
      · obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hz
        refine Finset.mem_image.mpr ⟨⟨x.val,Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,x.property⟩)⟩,Finset.mem_univ _,?_⟩
        exact hx
      · obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hb
        refine Finset.mem_image.mpr ⟨⟨x.val,Finset.mem_union_right _ x.property⟩,Finset.mem_univ _,?_⟩
        exact hx
  · ext v
    constructor
    · intro hv
      obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hv
      have hs:σ x.val∈complementTailDomain A T:=by
        rw [←hσ]
        exact Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩
      rcases Finset.mem_union.mp hs with hout | ht
      · apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨⟨σ x.val,(Finset.mem_sdiff.mp hout).2⟩,Finset.mem_univ _,?_⟩
        exact hx
      · apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨⟨σ x.val,ht⟩,Finset.mem_univ _,?_⟩
        exact hx
    · intro hv
      rcases Finset.mem_union.mp hv with hz | ht
      · obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hz
        have hxT:x.val∈complementTailDomain A T:=Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,x.property⟩)
        rw [←hσ] at hxT
        obtain ⟨y,hy,hyx⟩:=Finset.mem_image.mp hxT
        refine Finset.mem_image.mpr ⟨⟨y,hy⟩,Finset.mem_univ _,?_⟩
        have heq:complementHeadEmbedding A D B T hDA hTD σ hσ fC ⟨y,hy⟩=
            fC (complementDomainEmbedding hDA x):=by
          apply congrArg fC
          apply Subtype.ext
          exact hyx
        exact heq.trans hx
      · obtain ⟨x,_,hx⟩:=Finset.mem_image.mp ht
        have hxT:x.val∈complementTailDomain A T:=Finset.mem_union_right _ x.property
        rw [←hσ] at hxT
        obtain ⟨y,hy,hyx⟩:=Finset.mem_image.mp hxT
        refine Finset.mem_image.mpr ⟨⟨y,hy⟩,Finset.mem_univ _,?_⟩
        have heq:complementHeadEmbedding A D B T hDA hTD σ hσ fC ⟨y,hy⟩=
            fC (endpointDomainEmbedding hTD x):=by
          apply congrArg fC
          apply Subtype.ext
          exact hyx
        exact heq.trans hx
end Oberwolfach
