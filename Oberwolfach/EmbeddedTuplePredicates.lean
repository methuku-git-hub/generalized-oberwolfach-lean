module

public import Oberwolfach.MarkedPermutationEmbedding
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! Exact tuple transport when every coordinate of an admissible tuple
belongs to a fixed embedded vertex domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def embeddedTuplePredicateEquiv {I W V:Type*} (f:W↪V)
    (P:(I→V)→Prop) (Q:(I→W)→Prop)
    (hiff:∀ z,Q z↔P (f∘z)) (hrange:∀ z,P z→∀ i,z i∈Set.range f):
    {z:I→W // Q z}≃{z:I→V // P z} where
  toFun z:=⟨f∘z.val,(hiff z.val).mp z.property⟩
  invFun z:=⟨fun i=>Classical.choose (hrange z.val z.property i),by
    apply (hiff _).mpr
    have he:(f∘fun i=>Classical.choose (hrange z.val z.property i))=z.val:=by
      funext i;exact Classical.choose_spec (hrange z.val z.property i)
    rw [he];exact z.property⟩
  left_inv z:=by
    apply Subtype.ext
    funext i
    apply f.injective
    exact Classical.choose_spec (hrange (f∘z.val) ((hiff z.val).mp z.property) i)
  right_inv z:=by
    apply Subtype.ext
    funext i
    exact Classical.choose_spec (hrange z.val z.property i)

theorem embedded_tuple_predicate_card {I W V:Type*} [Fintype I] [Fintype W] [Fintype V]
    (f:W↪V) (P:(I→V)→Prop) (Q:(I→W)→Prop)
    (hiff:∀ z,Q z↔P (f∘z)) (hrange:∀ z,P z→∀ i,z i∈Set.range f):
    Fintype.card {z:I→W // Q z}=Fintype.card {z:I→V // P z}:=by
  classical
  exact Fintype.card_congr (embeddedTuplePredicateEquiv f P Q hiff hrange)

end Oberwolfach
