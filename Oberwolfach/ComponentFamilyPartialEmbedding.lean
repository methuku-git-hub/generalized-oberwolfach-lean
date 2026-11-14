module

public import Oberwolfach.ComponentFamilyGluing

@[expose] public section
/-! The maps on disjoint actual components define one injective partial
vertex map on their union, with no arbitrary extension outside that domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {A:Type}

theorem component_family_partial_embedding
    (F:SimpleGraph (Fin n)) (C:A→F.ConnectedComponent)
    (hC:Function.Injective C) (f:∀a,C a↪Fin n)
    (hdis:∀a b,a≠b→Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f b))):
    ∃ψ:{v:Fin n // ∃a,v∈(C a).supp}↪Fin n,
      ∀a (x:C a),ψ ⟨x.val,⟨a,x.property⟩⟩=f a x :=by
  obtain ⟨src,dst,hsrc,hdst⟩:=component_family_embeddings_glue F C hC f hdis
  let ec:=Equiv.ofInjective src src.injective
  let intoRange:{v:Fin n // ∃a,v∈(C a).supp}↪Set.range src:=
    ⟨fun v=>⟨v.val,by
      obtain ⟨a,ha⟩:=v.property
      exact ⟨⟨a,⟨v.val,ha⟩⟩,hsrc _⟩⟩,by
      intro x y h
      apply Subtype.ext
      have hv:=congrArg (fun z:Set.range src=>z.val) h
      exact hv⟩
  let ψ: {v:Fin n // ∃a,v∈(C a).supp}↪Fin n:=
    (intoRange.trans ec.symm.toEmbedding).trans dst
  refine ⟨ψ,?_⟩
  intro a x
  have he:intoRange ⟨x.val,⟨a,x.property⟩⟩=ec ⟨a,x⟩:=by
    apply Subtype.ext
    exact (hsrc ⟨a,x⟩).symm
  change dst (ec.symm (intoRange ⟨x.val,⟨a,x.property⟩⟩))=f a x
  rw [he,Equiv.symm_apply_apply,hdst]
end Oberwolfach
