module

public import Oberwolfach.OrdinaryProtectedDeepMonotonicity

@[expose] public section
/-! All earlier protected levels disappear from a later inner pair, so
only the most recent deletion can affect that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_union_inner_zero
    (R:I→SimpleGraph V) (S:I→V→U→Prop) (T:Finset V) (W:Finset U)
    (havoid:∀i,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker T W)):
    spanningRestriction (⨆i,ordinaryPhysicalGraph (R i) (S i)) (ordinaryInnerVertices T W)=⊥:=by
  apply le_antisymm
  · intro a b hab
    have hh:=(spanningRestriction_adj _ _ _ _).mp hab
    obtain ⟨i,hi⟩:∃i,(ordinaryPhysicalGraph (R i) (S i)).Adj a b:=by
      simpa only [SimpleGraph.iSup_adj] using hh.1
    have hinner:(spanningRestriction (ordinaryPhysicalGraph (R i) (S i)) (ordinaryInnerVertices T W)).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hi,hh.2.1,hh.2.2⟩
    have hzero:=ordinary_protected_inner_zero (R i) (S i) T W (havoid i)
    rw [hzero] at hinner
    exact hinner
  · exact bot_le

theorem ordinary_protected_earlier_levels_persist
    (G:SimpleGraph (V⊕U)) (R:I→SimpleGraph V) (S:I→V→U→Prop) (E:SimpleGraph (V⊕U))
    (T:Finset V) (W:Finset U)
    (havoid:∀i,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker T W)):
    spanningRestriction ((G\(⨆i,ordinaryPhysicalGraph (R i) (S i)))\E) (ordinaryInnerVertices T W)=
      spanningRestriction (G\E) (ordinaryInnerVertices T W):=by
  exact graph_spanning_after_two_deletions G (⨆i,ordinaryPhysicalGraph (R i) (S i)) E
    (ordinaryInnerVertices T W) (ordinary_protected_union_inner_zero R S T W havoid)

theorem ordinary_nested_protected_earlier_levels_persist
    (G:SimpleGraph (V⊕U)) (R:I→SimpleGraph V) (S:I→V→U→Prop) (E:SimpleGraph (V⊕U))
    (T:Finset V) (W:Finset U) (Told:I→Finset V) (Wold:I→Finset U)
    (hT:∀i,T⊆Told i) (hW:∀i,W⊆Wold i)
    (havoid:∀i,Disjoint (ordinaryPhysicalGraph (R i) (S i)) (ordinaryDeepBlocker (Told i) (Wold i))):
    spanningRestriction ((G\(⨆i,ordinaryPhysicalGraph (R i) (S i)))\E) (ordinaryInnerVertices T W)=
      spanningRestriction (G\E) (ordinaryInnerVertices T W):=by
  apply ordinary_protected_earlier_levels_persist
  intro i
  exact (havoid i).mono_right (ordinary_deep_blocker_mono T (Told i) W (Wold i) (hT i) (hW i))
end Oberwolfach
