module

public import Oberwolfach.CommonSelectedClassChanges

@[expose] public section
/-! Two-sided spoke changes increase common-class overlap by at most the
changes to the two selected classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem common_selected_class_overlap_shared_changes
    (π:Equiv.Perm V) (H H':Bool→V→U→Prop) (κ:V→Bool) (u u':U) (δ:ℝ)
    (hc:∀b z,(∑ x,if ¬(H b x z↔H' b x z) then (1:ℝ) else 0)≤δ):
    (((commonSelectedClass H' κ u u' false)∩(commonSelectedClass H' κ u u' true).image π).card:ℝ)≤
      ((commonSelectedClass H κ u u' false)∩(commonSelectedClass H κ u u' true).image π).card+4*δ:=by
  let T:=commonSelectedClass H κ u u'
  let T':=commonSelectedClass H' κ u u'
  have hsub:T' false∩(T' true).image π⊆
      (T false∩(T true).image π)∪(changed (T false) (T' false)∪(changed (T true) (T' true)).image π):=by
    intro x hx
    obtain ⟨h₀,hh⟩:=Finset.mem_inter.mp hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hh
    by_cases hOld₀:π y∈T false
    · by_cases hOldK:y∈T true
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hOld₀,Finset.mem_image.mpr ⟨y,hOldK,rfl⟩⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨y,by simp [changed,hy,hOldK],rfl⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      simp [changed,h₀,hOld₀]
  have hb:((T' false∩(T' true).image π).card:ℝ)≤
      ((T false∩(T true).image π).card:ℝ)+(changed (T false) (T' false)).card+
      (changed (T true) (T' true)).card:=by
    have ha: (T' false∩(T' true).image π).card≤
        (T false∩(T true).image π).card+(changed (T false) (T' false)).card+
          (changed (T true) (T' true)).card:=by
      calc
        _ ≤ ((T false∩(T true).image π)∪(changed (T false) (T' false)∪(changed (T true) (T' true)).image π)).card:=Finset.card_le_card hsub
        _ ≤ (T false∩(T true).image π).card+(changed (T false) (T' false)∪(changed (T true) (T' true)).image π).card:=Finset.card_union_le _ _
        _ ≤ (T false∩(T true).image π).card+((changed (T false) (T' false)).card+(changed (T true) (T' true)).card):=by
          gcongr
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
        _ = _ := by omega
    exact_mod_cast ha
  have h₀:=commonSelectedClass_changed_card H H' κ u u' δ hc false
  have hK:=commonSelectedClass_changed_card H H' κ u u' δ hc true
  change ((changed (T false) (T' false)).card:ℝ)≤2*δ at h₀
  change ((changed (T true) (T' true)).card:ℝ)≤2*δ at hK
  change ((T' false∩(T' true).image π).card:ℝ)≤_
  linarith only [hb,h₀,hK]
end Oberwolfach
