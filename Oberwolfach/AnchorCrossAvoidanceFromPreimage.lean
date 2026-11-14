module

public import Oberwolfach.ActualOldEmbeddingFromAnchors

@[expose] public section
/-! Agreement and injectivity turn the geometric statement that only
prescribed piece vertices use anchor labels into the required cross-avoidance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem anchor_cross_avoidance_from_piece_preimage
    {X V:Type} [DecidableEq X] (A P:Finset X)
    (f:{x // x∈A}↪V) (g:{x // x∈P}↪V)
    (hagree:∀x (hx:x∈A) (hy:x∈P),f ⟨x,hx⟩=g ⟨x,hy⟩)
    (hpreimage:∀y:{x // x∈A},f y∈Set.range g→y.val∈P):
    ∀x (hx:x∈P) (hxa:x∉A) (y:{x // x∈A}),g ⟨x,hx⟩≠f y:=by
  intro x hx hxa y he
  have hy:y.val∈P:=hpreimage y ⟨⟨x,hx⟩,he⟩
  have hh:g ⟨x,hx⟩=g ⟨y.val,hy⟩:=he.trans (hagree y.val y.property hy)
  have hxy:x=y.val:=congrArg Subtype.val (g.injective hh)
  exact hxa (hxy ▸ y.property)
end Oberwolfach
