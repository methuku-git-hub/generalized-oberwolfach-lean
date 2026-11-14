module

public import Oberwolfach.BufferedCanonicalComplementImages
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section
/-! A complement embedding extends to a bijection when the source and target
have the same size; the remaining target labels are precisely the images of
the deleted source vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem complement_embedding_extends_to_bijection
    {X V:Type*} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]
    (D:Finset X) (f:{x // x∉D}↪V) (hcard:Fintype.card X=Fintype.card V):
    ∃e:X≃V,(∀x:{x // x∉D},e x.val=f x) ∧
      Finset.univ\(Finset.univ.image f) = D.image e:=by
  classical
  obtain ⟨b⟩:=Fintype.card_eq.mp hcard
  obtain ⟨σ,hσ⟩:=Equiv.Perm.exists_extending_pair
    (fun x:{x // x∉D}=>b x.val) (fun x:{x // x∉D}=>f x)
    (b.injective.comp Subtype.val_injective) f.injective
  let e:X≃V:=b.trans σ
  refine ⟨e,?_,?_⟩
  · intro x
    exact hσ x
  · ext v
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro hv
      let x:=e.symm v
      have hx:x∈D:=by
        by_contra hn
        exact hv ⟨⟨x,hn⟩,by simpa [x,e] using (hσ ⟨x,hn⟩).symm⟩
      exact ⟨x,hx,by simp [x]⟩
    · rintro ⟨x,hx,hxv⟩ ⟨y,hy⟩
      have hxe:e x=f y:=hxv.trans hy.symm
      have hsame:x=y.val:=e.injective (by rw [hxe];exact (hσ y).symm)
      exact y.property (hsame ▸ hx)
end Oberwolfach
