module

public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Membership changes and samples retain their exact cardinalities under
an injective embedding of a row or hub class into the physical vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem changed_image_card {X Y:Type} [DecidableEq X] [DecidableEq Y]
    (f:X→Y) (hf:Function.Injective f) (A B:Finset X) :
    (changed (A.image f) (B.image f)).card=(changed A B).card := by
  have h₁ := Finset.image_sdiff (f:=f) A B hf
  have h₂ := Finset.image_sdiff (f:=f) B A hf
  have he:(changed A B).image f=changed (A.image f) (B.image f):=by
    simp only [changed,Finset.image_union]
    convert congrArg₂ (fun S T:Finset Y=>S∪T) h₁ h₂ using 1 <;> congr!

  rw [←he,Finset.card_image_of_injective _ hf]

theorem filter_image_class {X Y:Type} [DecidableEq X] [DecidableEq Y]
    (f:X→Y) (A:Finset X) (P:Y→Prop) :
    (A.image f).filter P=(A.filter (fun x=>P (f x))).image f := by
  ext y
  simp only [Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩;exact ⟨x,⟨hx,hp⟩,rfl⟩
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩;exact ⟨⟨x,hx,rfl⟩,hp⟩

end Oberwolfach
