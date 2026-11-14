module

public import Oberwolfach.FiniteFibreCounts

@[expose] public section

/-! Lower bounds on the number of images from upper bounds on fibres. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_image_fibre_card_bound {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (M : ℕ) (hM : ∀ b,Fintype.card {a : A // f a=b} ≤ M) :
    Fintype.card A ≤ (Finset.univ.image f).card*M := by
  let I := Finset.univ.image f
  let g (a : A) : I := ⟨f a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
  have hg (b : I) : Fintype.card {a : A // g a=b} ≤ M := by
    let enc (a : {a : A // g a=b}) : {a : A // f a=b.val} :=
      ⟨a.val,congrArg Subtype.val a.property⟩
    have hinj : Function.Injective enc := by
      intro x y he;apply Subtype.ext
      exact congrArg (fun z : {a : A // f a=b.val} => z.val) he
    have hh := Fintype.card_le_of_injective enc hinj
    apply hh.trans
    convert hM b.val using 1 <;> congr!
  have hh := finite_fibre_card_bound g M (by intro b;convert hg b using 1 <;> congr!)
  simpa only [Fintype.card_coe] using hh

end Oberwolfach
