module

public import Oberwolfach.OrdinaryProtectedInnerPersistence

@[expose] public section
/-! Avoidance of a deeper blocker persists for every still-smaller pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_blocker_mono (T T':Finset V) (W W':Finset U)
    (hT:T⊆T') (hW:W⊆W'):
    ordinaryDeepBlocker T W≤ordinaryDeepBlocker T' W':=by
  intro a b hab
  cases a with
  | inl v=>cases b with
    | inl w=>
      have hh:=(ordinary_deep_rim_blocker_adj T v w).mp hab
      exact (ordinary_deep_rim_blocker_adj T' v w).mpr ⟨hh.1,hT hh.2.1,hT hh.2.2⟩
    | inr u=>exact ⟨hT hab.1,hW hab.2⟩
  | inr u=>cases b with
    | inl v=>exact ⟨hT hab.1,hW hab.2⟩
    | inr z=>exact hab.elim

theorem ordinary_protected_inner_zero_nested (R:SimpleGraph V) (S:V→U→Prop)
    (T T':Finset V) (W W':Finset U) (hT:T⊆T') (hW:W⊆W')
    (havoid:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T' W')):
    spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices T W)=⊥:=by
  apply ordinary_protected_inner_zero R S T W
  exact havoid.mono_right (ordinary_deep_blocker_mono T T' W W' hT hW)
end Oberwolfach
