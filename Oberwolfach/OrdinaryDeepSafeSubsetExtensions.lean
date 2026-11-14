module

public import Oberwolfach.OrdinaryDeepSafeHost

@[expose] public section
/-! Every extension based outside the deeper vertex set is a valid
    extension in the deep-safe host, without a post-sampling loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_safe_subset_extensions (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (W:Finset U) (u:U) (a c:V):
    ((((X\T).filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ) ≤
      (((X.filter (fun v=>ordinaryDeepSafeSpokes H T W v u))∩
        (ordinaryDeepSafeRim Q T).neighborFinset a∩(ordinaryDeepSafeRim Q T).neighborFinset c).card:ℝ) :=by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset] at hv
  simp only [Finset.mem_inter,Finset.mem_filter,SimpleGraph.mem_neighborFinset,
    ordinaryDeepSafeSpokes,ordinaryDeepSpokeBlocker,ordinaryDeepSafeRim,SimpleGraph.sdiff_adj]
  refine ⟨⟨⟨hv.1.1.1.1,hv.1.1.2,?_⟩,hv.1.2,?_⟩,hv.2,?_⟩
  · intro h;exact hv.1.1.1.2 h.1
  · intro h;exact hv.1.1.1.2 ((ordinary_deep_rim_blocker_adj T a v).mp h).2.2
  · intro h;exact hv.1.1.1.2 ((ordinary_deep_rim_blocker_adj T c v).mp h).2.2
end Oberwolfach
