module

public import Oberwolfach.ResidualSpokeCardinality

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_spoke_card_from_complement_embedding_with_reserve
    {X V:Type*} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    (A D E:Finset X) (hDA:D⊆A) (hEA:E⊆A) (hED:Disjoint E D)
    (fC:{x // x∉D}↪V) (reserved:ℕ) (hcard:Fintype.card X+reserved=Fintype.card V)
    (R Z B:Finset V)
    (hZ:Z=Finset.univ.image ((complementDomainEmbedding hDA).trans fC))
    (hB:B=Finset.univ.image ((endpointDomainEmbedding hED).trans fC))
    (hR:R=Finset.univ\(Z∪B)) : R.card=reserved+A.card-E.card := by
  classical
  have hZcard:Z.card=Fintype.card X-A.card:=by
    rw [hZ,Finset.card_image_of_injective _ ((complementDomainEmbedding hDA).trans fC).injective]
    simpa using Fintype.card_subtype_compl (fun x:X=>x∈A)
  have hBcard:B.card=E.card:=by
    rw [hB,Finset.card_image_of_injective _ ((endpointDomainEmbedding hED).trans fC).injective]
    simp
  have hZB:Disjoint Z B:=by
    rw [hZ,hB]
    apply Finset.disjoint_left.mpr
    intro v hvz hvb
    obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hvz
    obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hvb
    have heq:fC (complementDomainEmbedding hDA x)=fC (endpointDomainEmbedding hED y):=hx.trans hy.symm
    have hxy:complementDomainEmbedding hDA x=endpointDomainEmbedding hED y:=fC.injective heq
    have hval:x.val=y.val:=congrArg (fun z:{x // x∉D}=>z.val) hxy
    exact x.property (hval.symm ▸ hEA y.property)
  rw [hR,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    Finset.card_union_of_disjoint hZB,hZcard,hBcard,←hcard]
  have hA:A.card≤Fintype.card X:=Finset.card_le_univ A
  have hE:E.card≤A.card:=Finset.card_le_card hEA
  omega
end Oberwolfach
