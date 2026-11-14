module

public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! In addition to edges added by an edit, require the complement matching
to cover every non-reference edge inside the protected inner set. Remove
those same sampled edges from the earlier matching's host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryProtectedRequired (Target Sample Reference:SimpleGraph V) (Inner:Finset V):SimpleGraph V :=
  (Target\Sample) ⊔ spanningRestriction (Target\Reference) Inner

def ordinaryProtectedSampleDeletion (Sample Target Reference Protect:SimpleGraph V) (Inner:Finset V):SimpleGraph V :=
  (Sample\Target) ⊔ Protect ⊔ spanningRestriction (Sample\Reference) Inner

theorem ordinary_protected_required_edges_relations
    (Target Sample Reference Protect:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference):
    let G:=ordinaryProtectedRequired Target Sample Reference Inner
    let Del:=ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner;
    G≤Target\Protect ∧ Sample\Del≤Target\Protect ∧
    (∀v∈Inner,∀w∈Inner,(Target\G).Adj v w→Reference.Adj v w) ∧
    (∀v w,G.Adj v w→¬(Sample\Del).Adj v w):=by
  intro G Del
  constructor
  · intro v w he
    change (Target\Sample).Adj v w ∨ (spanningRestriction (Target\Reference) Inner).Adj v w at he
    rcases he with he|he
    · exact ⟨he.1,fun hp=>he.2 (hRef (hProtect hp))⟩
    · have hh:=(spanningRestriction_adj (Target\Reference) Inner v w).mp he
      exact ⟨hh.1.1,fun hp=>hh.1.2 (hProtect hp)⟩
  constructor
  · intro v w he
    refine ⟨?_,?_⟩
    · by_contra ht
      have hdel:Del.Adj v w:=by
        change ((Sample\Target)⊔Protect).Adj v w ∨ (spanningRestriction (Sample\Reference) Inner).Adj v w
        exact Or.inl (Or.inl ⟨he.1,ht⟩)
      exact he.2 hdel
    · intro hp
      have hdel:Del.Adj v w:=by
        change ((Sample\Target)⊔Protect).Adj v w ∨ (spanningRestriction (Sample\Reference) Inner).Adj v w
        exact Or.inl (Or.inr hp)
      exact he.2 hdel
  constructor
  · intro v hv w hw he
    by_contra href
    have hg:G.Adj v w:=by
      change (Target\Sample).Adj v w ∨ (spanningRestriction (Target\Reference) Inner).Adj v w
      exact Or.inr ((spanningRestriction_adj (Target\Reference) Inner v w).mpr ⟨⟨he.1,href⟩,hv,hw⟩)
    exact he.2 hg
  · intro v w hg hs
    change (Target\Sample).Adj v w ∨ (spanningRestriction (Target\Reference) Inner).Adj v w at hg
    rcases hg with ha|hi
    · exact ha.2 hs.1
    · have hh:=(spanningRestriction_adj (Target\Reference) Inner v w).mp hi
      have hdel:Del.Adj v w:=by
        change ((Sample\Target)⊔Protect).Adj v w ∨ (spanningRestriction (Sample\Reference) Inner).Adj v w
        exact Or.inr ((spanningRestriction_adj (Sample\Reference) Inner v w).mpr ⟨⟨hs.1,hh.1.2⟩,hh.2.1,hh.2.2⟩)
      exact hs.2 hdel
end Oberwolfach
