module

public import Oberwolfach.BufferedComplementImage

@[expose] public section
/-! A glued completion image has precise one-sided bounds after path-domain
vertices are excluded.  Endpoint images account for the difference. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype X] [DecidableEq X] [DecidableEq V]

theorem complement_image_decomposition_bounds
    (interior full old remaining:Finset X) (Y End:Finset V)
    (ψ:X→V) (Φ:{x // x∈remaining}→V) (f:{x // x∉interior}→V)
    (hfull:interior⊆full) (hcover:old∪remaining=Finset.univ)
    (hremain:Disjoint interior remaining)
    (hold:∀x:{x // x∉interior},x.val∈old→f x=ψ x.val)
    (hnew:∀x:{x // x∈remaining},∀hx:x.val∉interior,f ⟨x.val,hx⟩=Φ x)
    (hend:∀x:{x // x∉interior},x.val∈full→f x∈Y∪End):
    let Outside:Finset V:=(Finset.univ.filter (fun x:{x // x∉interior}=>x.val∉full)).image f
    let Old:Finset V:=(old\interior).image ψ
    let New:Finset V:=Finset.univ.image Φ;
    Outside⊆Old∪New ∧ Old⊆Y∪(Outside∪End) ∧ New⊆Y∪(Outside∪End):=by
  intro Outside Old New
  constructor
  · intro v hv
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hv
    have hxcover:x.val∈old∪remaining:=by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hxcover with ho|hr
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨x.val,Finset.mem_sdiff.mpr ⟨ho,x.property⟩,(hold x ho).symm.trans hxv⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨⟨x.val,hr⟩,Finset.mem_univ _,(hnew ⟨x.val,hr⟩ x.property).symm.trans hxv⟩
  · constructor
    · intro v hv
      obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hv
      have ho: x∈old:=(Finset.mem_sdiff.mp hx).1
      have hi: x∉interior:=(Finset.mem_sdiff.mp hx).2
      by_cases hf:x∈full
      · have he:=hend ⟨x,hi⟩ hf
        rw [hold ⟨x,hi⟩ ho,hxv] at he
        rcases Finset.mem_union.mp he with hy|he
        · exact Finset.mem_union_left _ hy
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ he)
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨⟨x,hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,(hold ⟨x,hi⟩ ho).trans hxv⟩
    · intro v hv
      obtain ⟨x,_,hxv⟩:=Finset.mem_image.mp hv
      have hi:x.val∉interior:=fun h=>(Finset.disjoint_left.mp hremain) h x.property
      by_cases hf:x.val∈full
      · have he:=hend ⟨x.val,hi⟩ hf
        rw [hnew x hi,hxv] at he
        rcases Finset.mem_union.mp he with hy|he
        · exact Finset.mem_union_left _ hy
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ he)
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨⟨x.val,hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,(hnew x hi).trans hxv⟩
end Oberwolfach
