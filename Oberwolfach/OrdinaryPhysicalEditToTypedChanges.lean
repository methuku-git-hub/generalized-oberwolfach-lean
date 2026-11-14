module

public import Oberwolfach.OrdinaryPhysicalFullChangeBounds

@[expose] public section
/-! A single physical symmetric-edit bound controls all rim and spoke
    row/column changes on the very same pair of hosts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_edit_to_typed_changes
    (R Q:SimpleGraph V) (H J:V→U→Prop) (L:ℝ)
    (h:∀z:V⊕U,((changed ((ordinaryPhysicalGraph R H).neighborFinset z)
      ((ordinaryPhysicalGraph Q J).neighborFinset z)).card:ℝ)≤L):
    (∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) ∧
    (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):=by
  constructor
  · intro v
    have hsub:(changed (R.neighborFinset v) (Q.neighborFinset v)).image (Sum.inl:V→V⊕U) ⊆
        changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inl v))
          ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inl v)):=by
      intro z hz
      obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hz
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset]
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,ordinaryPhysicalGraph] using hw
    have hc:((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤
        ((changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inl v))
          ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inl v))).card:ℝ):=by
      have hh:=Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Sum.inl_injective] at hh
      exact_mod_cast hh
    exact hc.trans (h (Sum.inl v))
  constructor
  · intro v
    have hsub:(changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).image (Sum.inr:U→V⊕U) ⊆
        changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inl v))
          ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inl v)):=by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset]
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
        SimpleGraph.mem_neighborFinset,ordinaryPhysicalGraph] using hu
    have hc:((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤
        ((changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inl v))
          ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inl v))).card:ℝ):=by
      have hh:=Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Sum.inr_injective] at hh
      exact_mod_cast hh
    exact hc.trans (h (Sum.inl v))
  · intro u
    have hsub:(changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).image (Sum.inl:V→V⊕U) ⊆
        changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inr u))
          ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inr u)):=by
      intro z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset]
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
        SimpleGraph.mem_neighborFinset,ordinaryPhysicalGraph] using hv
    have hc:((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤
        ((changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inr u))
          ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inr u))).card:ℝ):=by
      have hh:=Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Sum.inl_injective] at hh
      exact_mod_cast hh
    exact hc.trans (h (Sum.inr u))
end Oberwolfach
