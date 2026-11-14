module

public import Oberwolfach.MarkedTransformerAssignments
public import Oberwolfach.FiniteTypedBijection

@[expose] public section

/-! The two attachment bijections at a row root. Incoming marked rim
incidences receive exactly the marked incoming spoke attachments; every
hub occurrence avoids the attachment of its own rim path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem marked_attachment_pairings {X Y S:Type*} [Fintype X] [Fintype Y] [Fintype S]
    (K:Finset X) (SK:Finset S)
    (hXY:Fintype.card X=Fintype.card Y) (hXS:Fintype.card X=Fintype.card S)
    (hK:K.card=SK.card) (hs:0<Fintype.card X)
    (hpad:¬(Fintype.card X=1∧K.card=1)):
    ∃ σ:Equiv.Perm (X⊕Y),∃ a:X≃S,∃ b:Y≃S,
      (∀ x,σ x≠x)∧
      (∀ x∈K,∃ y:X,σ (Sum.inl x)=Sum.inl y)∧
      (∀ x:X,a x∈SK↔σ.symm (Sum.inl x)∈K.image (Sum.inl (β:=Y)))∧
      ∀ y:Y,σ.symm (Sum.inr y)∉K.image (Sum.inl (β:=Y)):=by
  classical
  let J:Finset (X⊕Y):=K.image Sum.inl
  let A:Finset (X⊕Y):=Finset.univ.image (Sum.inl (β:=Y))
  have hJ:J.card=K.card:=Finset.card_image_of_injective _ Sum.inl_injective
  have hA:A.card=Fintype.card X:=by
    dsimp only [A]
    rw [Finset.card_image_of_injective _ Sum.inl_injective,Finset.card_univ]
  have hm:=marked_transformer_assignment_margins (Fintype.card X) K.card (Finset.card_le_univ K) hs hpad
  obtain ⟨σ,hσ,hmark⟩:=marked_transformer_attachment_assignment (Equiv.refl (X⊕Y)) J A
    (by rw [hJ,hA];exact Finset.card_le_univ K)
    (by rw [hJ,hA];exact hm.1)
    (by rw [Fintype.card_sum,← hXY,hJ];omega)
  have hx:∀ x:K,∃ y:X,σ (Sum.inl x.val)=Sum.inl y:=by
    intro x
    have hh:=hmark (Sum.inl x.val) (Finset.mem_image.mpr ⟨x.val,x.property,rfl⟩)
    obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hh
    exact ⟨y,hy.symm⟩
  choose g hg using hx
  have hgi:Function.Injective g:=by
    intro x y he
    apply Subtype.ext
    exact Sum.inl.inj (σ.injective ((hg x).trans ((congrArg Sum.inl he).trans (hg y).symm)))
  let T:Finset X:=Finset.univ.image g
  have hT:T.card=K.card:=by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hgi,Finset.card_univ,Fintype.card_coe]
  obtain ⟨a,ha⟩:=finite_bijection_preserving_predicate (fun x:X=>x∈T) (fun s:S=>s∈SK) hXS
    (by simpa only [Fintype.card_coe] using hT.trans hK)
  let b:Y≃S:=Fintype.equivOfCardEq (hXY.symm.trans hXS)
  have ht (x:X):x∈T↔σ.symm (Sum.inl x)∈J:=by
    constructor
    · intro hh
      obtain ⟨z,_,hz⟩:=Finset.mem_image.mp hh
      have he:σ (Sum.inl z.val)=Sum.inl x:=(hg z).trans (congrArg Sum.inl hz)
      have he':σ.symm (Sum.inl x)=Sum.inl z.val:=by rw [← he,Equiv.symm_apply_apply]
      rw [he']
      exact Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩
    · intro hh
      obtain ⟨z,hz,he⟩:=Finset.mem_image.mp hh
      refine Finset.mem_image.mpr ⟨⟨z,hz⟩,Finset.mem_univ _,?_⟩
      apply Sum.inl_injective (β:=Y)
      rw [← hg]
      have he':=congrArg σ he
      simpa only [Equiv.apply_symm_apply] using he'
  refine ⟨σ,a,b,hσ,?_,fun x=>(ha x).trans (ht x),?_⟩
  · intro x hx
    exact ⟨g ⟨x,hx⟩,hg ⟨x,hx⟩⟩
  · intro y hy
    have hh:=hmark (σ.symm (Sum.inr y)) hy
    rw [Equiv.apply_symm_apply] at hh
    obtain ⟨x,_,he⟩:=Finset.mem_image.mp hh
    exact Sum.inl_ne_inr he

end Oberwolfach
