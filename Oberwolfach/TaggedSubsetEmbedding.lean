module

public import Oberwolfach.MarkedEndpointAssignments

@[expose] public section

/-! Removing the type tag is injective only for disjoint underlying sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def taggedSubsetEmbedding {Z : Type} (A B : Finset Z) (h : Disjoint A B) : A⊕B ↪ Z where
  toFun := taggedSubsetValue A B
  inj' := by
    intro a b he
    cases a with
    | inl a=>cases b with
      | inl b=>exact congrArg Sum.inl (Subtype.ext he)
      | inr b=>
        have he' : a.val=b.val := he
        exact False.elim (Finset.disjoint_left.mp h a.property (he'.symm ▸ b.property))
    | inr a=>cases b with
      | inl b=>
        have he' : a.val=b.val := he
        exact False.elim (Finset.disjoint_left.mp h b.property (he' ▸ a.property))
      | inr b=>exact congrArg Sum.inr (Subtype.ext he)

theorem tagged_right_card {Z : Type} (A B : Finset Z) :
    (Finset.univ.filter (fun a : A⊕B=>a.isRight=true)).card=B.card := by
  classical
  have hh := Fintype.card_congr (typedSumRightEquiv A B)
  simpa only [Fintype.card_subtype,Fintype.card_coe] using hh

theorem tagged_left_card {Z : Type} (A B : Finset Z) :
    (Finset.univ.filter (fun a : A⊕B=>¬a.isRight=true)).card=A.card := by
  classical
  have hh := Fintype.card_congr (typedSumLeftEquiv A B)
  simpa only [Fintype.card_subtype,Fintype.card_coe] using hh

end Oberwolfach
