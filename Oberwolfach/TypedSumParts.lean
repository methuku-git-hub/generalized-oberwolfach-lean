module

public import Oberwolfach.BipartiteBlockTransport

@[expose] public section

/-! The two type classes of a tagged union are kept distinct even when
their labels coincide. Bijections here remove a tag only after fixing it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def typedSumRightEquiv (X Y : Type) : {a : X⊕Y // a.isRight=true} ≃ Y where
  toFun a := by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl x=>exact False.elim (Bool.false_ne_true ha)
    | inr y=>exact y
  invFun y := ⟨Sum.inr y,rfl⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl x=>exact False.elim (Bool.false_ne_true ha)
    | inr y=>rfl
  right_inv y := rfl

def typedSumLeftEquiv (X Y : Type) : {a : X⊕Y // ¬a.isRight=true} ≃ X where
  toFun a := by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl x=>exact x
    | inr y=>exact False.elim (ha rfl)
  invFun x := ⟨Sum.inl x,Bool.false_ne_true⟩
  left_inv a := by
    rcases a with ⟨a,ha⟩
    cases a with
    | inl x=>rfl
    | inr y=>exact False.elim (ha rfl)
  right_inv x := rfl

 theorem typedSumRightEquiv_label {X Y Z : Type} (f : X→Z) (g : Y→Z)
    (a : {a : X⊕Y // a.isRight=true}) :
    Sum.elim f g a.val=g (typedSumRightEquiv X Y a) := by
  rcases a with ⟨a,ha⟩
  cases a with
  | inl x=>exact False.elim (Bool.false_ne_true ha)
  | inr y=>rfl

 theorem typedSumLeftEquiv_label {X Y Z : Type} (f : X→Z) (g : Y→Z)
    (a : {a : X⊕Y // ¬a.isRight=true}) :
    Sum.elim f g a.val=f (typedSumLeftEquiv X Y a) := by
  rcases a with ⟨a,ha⟩
  cases a with
  | inl x=>rfl
  | inr y=>exact False.elim (ha rfl)

end Oberwolfach
