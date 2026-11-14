module

public import Oberwolfach.BoundedMatrixVertexRestriction

@[expose] public section

/-! Exact two-step neighbourhood losses under vertex restriction and
changes to the two incident relations. All endpoints remain fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type*} [Fintype V] [Fintype W] [DecidableEq V]

theorem relation_two_step_count_eq (R:V→V→Prop) (x y:V):
    ((Finset.univ.filter (fun z=>R x z∧R z y)).card:ℝ)=
      ∑ z,if R x z∧R z y then (1:ℝ) else 0:=by
  simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem relation_two_step_vertex_restriction (f:W↪V) (R:V→V→Prop) (x y:W):
    |((Finset.univ.filter (fun z=>R (f x) (f z)∧R (f z) (f y))).card:ℝ)-
      (Finset.univ.filter (fun z=>R (f x) z∧R z (f y))).card|≤
      (Finset.univ\Finset.univ.image f).card:=by
  have hh:=finite_bounded_sum_restriction (Finset.univ.image f) Finset.univ
    (Finset.subset_univ _) (fun z=>if R (f x) z∧R z (f y) then (1:ℝ) else 0)
    (by intro z _;split_ifs <;> norm_num)
  rw [Finset.sum_image (fun _ _ _ _ he=>f.injective he)] at hh
  simpa only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using hh

theorem relation_two_step_changes (R Q:V→V→Prop) (x y:V) (δout δin:ℝ)
    (hout:(∑ z,if ¬(R x z↔Q x z) then (1:ℝ) else 0)≤δout)
    (hin:(∑ z,if ¬(R z y↔Q z y) then (1:ℝ) else 0)≤δin):
    |((Finset.univ.filter (fun z=>Q x z∧Q z y)).card:ℝ)-
      (Finset.univ.filter (fun z=>R x z∧R z y)).card|≤δout+δin:=by
  rw [relation_two_step_count_eq,relation_two_step_count_eq]
  apply (finset_indicator_sum_change Finset.univ _ _).trans
  calc
    _ ≤ ∑ z,((if ¬(R x z↔Q x z) then (1:ℝ) else 0)+(if ¬(R z y↔Q z y) then (1:ℝ) else 0)):=by
      apply Finset.sum_le_sum
      intro z _
      by_cases h1:R x z <;> by_cases h2:R z y <;> by_cases h3:Q x z <;> by_cases h4:Q z y <;>
        norm_num [h1,h2,h3,h4]
    _ ≤ δout+δin:=by rw [Finset.sum_add_distrib];exact add_le_add hout hin

end Oberwolfach
