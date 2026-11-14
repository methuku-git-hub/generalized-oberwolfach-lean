module

public import Oberwolfach.OrdinaryPostmatchingRequired

@[expose] public section
/-! Covering the post-matching demands suffices for the same remainder to
lie in the sample, avoid the forbidden graph and agree on the protected pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_postmatching_complement_agreement
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Protect Bad Used New:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hBad:Disjoint Reference Bad)
    (hInner:spanningRestriction Reference Inner≤Protect)
    (hTarget:∀v∈Inner,∀w∈Inner,Target.Adj v w↔Sample.Adj v w)
    (hUsed:Used≤Target\Protect) (hNew:New≤Target\Protect)
    (hCover:ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner≤New):
    let Rem:=Target\(Used⊔New);
    Rem≤Sample ∧ Disjoint Rem Bad ∧
      (∀v∈Inner,∀w∈Inner,Rem.Adj v w↔Reference.Adj v w) :=by
  intro Rem
  have hRel:=ordinary_postmatching_required_relations Target Sample Reference Protect Bad Used Inner hRef hProtect hBad
  have hcov:ordinaryForbiddenRequired Target Sample Reference Bad Inner≤Used⊔New:=by
    intro x y h
    rcases hRel.2.2.1 h with h|h
    · exact Or.inl h
    · exact Or.inr (hCover h)
  have hAdded:(Target\Sample)≤Used⊔New:=by
    intro x y h
    apply hcov
    exact Or.inl (Or.inl h)
  have hB:Target⊓Bad≤Used⊔New:=by
    intro x y h
    apply hcov
    exact Or.inr h
  refine ⟨?_,?_,?_⟩
  · intro x y h
    by_contra hs
    exact h.2 (hAdded ⟨h.1,hs⟩)
  · apply disjoint_iff_inf_le.mpr
    intro x y h
    exact h.1.2 (hB ⟨h.1.1,h.2⟩)
  · intro v hv w hw
    constructor
    · intro h
      by_contra hr
      have hg:(ordinaryForbiddenRequired Target Sample Reference Bad Inner).Adj v w:=by
        exact Or.inl (Or.inr ((spanningRestriction_adj (Target\Reference) Inner v w).mpr ⟨⟨h.1,hr⟩,hv,hw⟩))
      exact h.2 (hcov hg)
    · intro hr
      have ht:Target.Adj v w:=(hTarget v hv w hw).mpr (hRef hr)
      have hp:Protect.Adj v w:=hInner ((spanningRestriction_adj Reference Inner v w).mpr ⟨hr,hv,hw⟩)
      refine ⟨ht,?_⟩
      intro h
      rcases h with h|h
      · exact (hUsed h).2 hp
      · exact (hNew h).2 hp
end Oberwolfach
