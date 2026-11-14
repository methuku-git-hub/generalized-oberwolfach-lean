module

public import Oberwolfach.SelectedCommonConfigurationMaps
public import Oberwolfach.MarkedBalanceSpokeChanges
public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Deterministic class-size and overlap bounds for one fixed selector.
Both additions and deletions are charged to actual spoke changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem selectedSpokes_change_columns (H H' : Bool→V→U→Prop) (κ : V→Bool) (δ : ℝ)
    (hc : ∀ b u,(∑ x,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δ) :
    ∀ b u,(∑ x,if ¬(selectedSpokes H κ b x u↔selectedSpokes H' κ b x u) then (1:ℝ) else 0)≤δ := by
  intro b u
  apply le_trans _ (hc b u)
  apply Finset.sum_le_sum
  intro x hx
  by_cases he : H b x u↔H' b x u
  · have hh : selectedSpokes H κ b x u↔selectedSpokes H' κ b x u := and_congr he Iff.rfl
    simp only [he,hh,not_true_eq_false,ite_false,le_refl]
  · simp only [he,not_false_eq_true,ite_true]
    split_ifs <;> norm_num

theorem commonSelectedClass_changed_card (H H' : Bool→V→U→Prop) (κ : V→Bool) (u u' : U)
    (δ : ℝ) (hc : ∀ b z,(∑ x,if ¬(H b x z↔H' b x z) then (1:ℝ) else 0)≤δ) (b : Bool) :
    ((changed (commonSelectedClass H κ u u' b) (commonSelectedClass H' κ u u' b)).card:ℝ)≤2*δ := by
  have he : changed (commonSelectedClass H κ u u' b) (commonSelectedClass H' κ u u' b)=
      Finset.univ.filter (fun x=>¬(commonThinnedSpokes H κ u u' b x ()↔commonThinnedSpokes H' κ u u' b x ())) := by
    ext x
    simp only [changed,commonSelectedClass,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [he,Finset.card_filter,Nat.cast_sum]
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have hh := commonThinnedSpokes_change_columns H H' κ u u' δ hc b
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  unfold bipAdj
  split_ifs <;> first | rfl | (exfalso;tauto)

theorem commonSelectedClass_card_change (H H' : Bool→V→U→Prop) (κ : V→Bool) (u u' : U)
    (δ : ℝ) (hc : ∀ b z,(∑ x,if ¬(H b x z↔H' b x z) then (1:ℝ) else 0)≤δ) (b : Bool) :
    |((commonSelectedClass H' κ u u' b).card:ℝ)-(commonSelectedClass H κ u u' b).card|≤2*δ := by
  rw [abs_sub_comm]
  exact (card_difference_le_changed _ _).trans (commonSelectedClass_changed_card H H' κ u u' δ hc b)

theorem commonSelectedClass_overlap_change (π : Equiv.Perm V)
    (H H' : Bool→V→U→Prop) (κ : V→Bool) (u u' : U) (δ : ℝ)
    (hc : ∀ b z,(∑ x,if ¬(H b x z↔H' b x z) then (1:ℝ) else 0)≤δ)
    (hdis : Disjoint (commonSelectedClass H κ u u' false) ((commonSelectedClass H κ u u' true).image π)) :
    (((commonSelectedClass H' κ u u' false)∩(commonSelectedClass H' κ u u' true).image π).card:ℝ)≤4*δ := by
  let T := commonSelectedClass H κ u u'
  let T' := commonSelectedClass H' κ u u'
  have hsub : T' false∩(T' true).image π⊆changed (T false) (T' false)∪(changed (T true) (T' true)).image π := by
    intro x hx
    obtain ⟨h₀,hh⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hh
    by_cases hOld₀ : π y∈T false
    · by_cases hOldK : y∈T true
      · exact False.elim (Finset.disjoint_left.mp hdis hOld₀ (Finset.mem_image.mpr ⟨y,hOldK,rfl⟩))
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨y,by simp [changed,hy,hOldK],rfl⟩
    · apply Finset.mem_union_left
      simp [changed,h₀,hOld₀]
  have hb := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have him := Finset.card_image_le (s:=changed (T true) (T' true)) (f:=π)
  have hbR : ((T' false∩(T' true).image π).card:ℝ)≤(changed (T false) (T' false)).card+(changed (T true) (T' true)).card := by
    exact_mod_cast hb.trans (Nat.add_le_add_left him _)
  have h₀ := commonSelectedClass_changed_card H H' κ u u' δ hc false
  have hK := commonSelectedClass_changed_card H H' κ u u' δ hc true
  change ((T' false∩(T' true).image π).card:ℝ)≤_
  change ((changed (T false) (T' false)).card:ℝ)≤2*δ at h₀
  change ((changed (T true) (T' true)).card:ℝ)≤2*δ at hK
  linarith only [hbR,h₀,hK]

end Oberwolfach
