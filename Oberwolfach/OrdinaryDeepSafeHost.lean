module

public import Oberwolfach.OrdinaryDeepBlocker
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! Remove only the resources of a deeper pair.  Every original common
extension outside the deeper rim set survives, and outside--outside resources
are unchanged when the deeper pair is nested in the current pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryDeepSafeRim (Q:SimpleGraph V) (T:Finset V):SimpleGraph V := Q\ordinaryDeepRimBlocker T

def ordinaryDeepSafeSpokes (H:V→U→Prop) (T:Finset V) (W:Finset U):V→U→Prop :=
  fun v u=>H v u ∧ ¬ordinaryDeepSpokeBlocker T W v u

theorem ordinary_deep_safe_physical (Q:SimpleGraph V) (H:V→U→Prop) (T:Finset V) (W:Finset U):
    ordinaryPhysicalGraph (ordinaryDeepSafeRim Q T) (ordinaryDeepSafeSpokes H T W)=
      ordinaryPhysicalGraph Q H\ordinaryDeepBlocker T W := by
  ext x y
  cases x <;> cases y <;> simp [ordinaryPhysicalGraph,ordinaryDeepSafeRim,ordinaryDeepSafeSpokes,ordinaryDeepBlocker]

theorem ordinary_deep_safe_extensions (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (W:Finset U) (u:U) (a c:V):
    (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ) ≤
      (((X.filter (fun v=>ordinaryDeepSafeSpokes H T W v u))∩
        (ordinaryDeepSafeRim Q T).neighborFinset a∩(ordinaryDeepSafeRim Q T).neighborFinset c).card:ℝ)+T.card := by
  let S:Finset V := (X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c
  let S':Finset V := (X.filter (fun v=>ordinaryDeepSafeSpokes H T W v u))∩
        (ordinaryDeepSafeRim Q T).neighborFinset a∩(ordinaryDeepSafeRim Q T).neighborFinset c
  have hsub:S\T⊆S' := by
    intro v hv
    have hvS: v∈S := (Finset.mem_sdiff.mp hv).1
    have hvT: v∉T := (Finset.mem_sdiff.mp hv).2
    simp only [S,Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset] at hvS
    simp only [S',Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset,
      ordinaryDeepSafeSpokes,ordinaryDeepSpokeBlocker,ordinaryDeepSafeRim,SimpleGraph.sdiff_adj]
    refine ⟨⟨⟨hvS.1.1.1, hvS.1.1.2, ?_⟩,hvS.1.2,?_⟩,hvS.2,?_⟩
    · intro h;exact hvT h.1
    · intro h;exact hvT ((ordinary_deep_rim_blocker_adj T a v).mp h).2.2
    · intro h;exact hvT ((ordinary_deep_rim_blocker_adj T c v).mp h).2.2
  have hc:=Finset.card_sdiff_add_card_inter S T
  have hi:(S∩T).card≤T.card:=Finset.card_le_card Finset.inter_subset_right
  have hs:(S\T).card≤S'.card:=Finset.card_le_card hsub
  have hn:S.card≤S'.card+T.card:=by omega
  exact_mod_cast hn

theorem ordinary_deep_safe_outside_rim (Q:SimpleGraph V) (X T:Finset V) (hTX:T⊆X)
    (v w:V) (hv:v∉X) (hw:w∉X):
    (ordinaryDeepSafeRim Q T).Adj v w ↔ Q.Adj v w := by
  simp only [ordinaryDeepSafeRim,SimpleGraph.sdiff_adj]
  constructor
  · exact And.left
  · intro h
    refine ⟨h,?_⟩
    intro hb
    exact hv (hTX ((ordinary_deep_rim_blocker_adj T v w).mp hb).2.1)

theorem ordinary_deep_safe_outside_spoke (H:V→U→Prop) (X T:Finset V) (W:Finset U)
    (hTX:T⊆X) (v:V) (u:U) (hv:v∉X):
    ordinaryDeepSafeSpokes H T W v u ↔ H v u := by
  simp only [ordinaryDeepSafeSpokes,ordinaryDeepSpokeBlocker]
  exact ⟨And.left,fun h=>⟨h,fun hb=>hv (hTX hb.1)⟩⟩
end Oberwolfach
