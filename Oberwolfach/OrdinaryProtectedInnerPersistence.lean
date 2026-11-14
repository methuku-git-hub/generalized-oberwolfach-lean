module

public import Oberwolfach.OrdinaryDeepBlocker

@[expose] public section
/-! A wheel family avoiding a deeper blocker deletes no physical edge
inside that deeper pair, even after later deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_inner_le_deep_blocker (R:SimpleGraph V) (S:V→U→Prop)
    (T:Finset V) (W:Finset U):
    spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices T W)≤ordinaryDeepBlocker T W:=by
  intro a b hab
  have hh:=(spanningRestriction_adj _ _ _ _).mp hab
  cases a with
  | inl v=>cases b with
    | inl w=>
      apply (ordinary_deep_rim_blocker_adj T v w).mpr
      have hr:R.Adj v w:=hh.1
      exact ⟨hr.ne,(ordinaryInnerVertices_left T W v).mp hh.2.1,(ordinaryInnerVertices_left T W w).mp hh.2.2⟩
    | inr u=>exact ⟨(ordinaryInnerVertices_left T W v).mp hh.2.1,(ordinaryInnerVertices_right T W u).mp hh.2.2⟩
  | inr u=>cases b with
    | inl v=>exact ⟨(ordinaryInnerVertices_left T W v).mp hh.2.2,(ordinaryInnerVertices_right T W u).mp hh.2.1⟩
    | inr z=>exact hh.1.elim

theorem ordinary_protected_inner_zero (R:SimpleGraph V) (S:V→U→Prop)
    (T:Finset V) (W:Finset U)
    (havoid:Disjoint (ordinaryPhysicalGraph R S) (ordinaryDeepBlocker T W)):
    spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices T W)=⊥:=by
  apply le_antisymm
  · intro a b hab
    have hphys:=((spanningRestriction_adj _ _ _ _).mp hab).1
    have hblock:=ordinary_physical_inner_le_deep_blocker R S T W hab
    exact (disjoint_iff_inf_le.mp havoid) ⟨hphys,hblock⟩
  · exact bot_le

theorem graph_spanning_sdiff_of_inner_zero {W:Type} (G D:SimpleGraph W) (X:Finset W)
    (hzero:spanningRestriction D X=⊥):
    spanningRestriction (G\D) X=spanningRestriction G X:=by
  ext a b
  simp only [spanningRestriction_adj,SimpleGraph.sdiff_adj]
  constructor
  · rintro ⟨⟨hg,_⟩,ha,hb⟩
    exact ⟨hg,ha,hb⟩
  · rintro ⟨hg,ha,hb⟩
    refine ⟨⟨hg,?_⟩,ha,hb⟩
    intro hd
    have hh:(spanningRestriction D X).Adj a b:=(spanningRestriction_adj _ _ _ _).mpr ⟨hd,ha,hb⟩
    rw [hzero] at hh
    exact hh

theorem graph_spanning_after_two_deletions {W:Type} (G D E:SimpleGraph W) (X:Finset W)
    (hzero:spanningRestriction D X=⊥):
    spanningRestriction ((G\D)\E) X=spanningRestriction (G\E) X:=by
  have hcomm:((G\D)\E)=((G\E)\D):=by
    ext a b;simp only [SimpleGraph.sdiff_adj];tauto
  rw [hcomm]
  exact graph_spanning_sdiff_of_inner_zero (G\E) D X hzero
end Oberwolfach
