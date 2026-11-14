module

public import Oberwolfach.SignedDemandNormalization
public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section

/-! Restricting actual edge occurrences subtracts their realised degree
loss from the original degree. The supplied comparison target is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype E]

theorem occurrenceDegree_restricted (f : E → V) (keep : E → Prop) (x : V) :
    occurrenceDegree (fun e : {e // keep e}=>f e.val) x=
      ∑ e,if keep e ∧ f e=x then (1:ℝ) else 0 := by
  have hh := finite_sum_restrict_of_zero keep (fun e=>if keep e ∧ f e=x then (1:ℝ) else 0)
    (by intro e he;simp only [he,false_and,ite_false])
  calc
    _ = ∑ e : {e // keep e},if keep e.val ∧ f e.val=x then (1:ℝ) else 0 := by
      unfold occurrenceDegree
      apply Finset.sum_congr rfl
      intro e _
      simp only [e.property,true_and]
    _ = _ := hh.symm

theorem occurrenceDegree_restriction_loss (f : E → V) (keep : E → Prop) (x : V) :
    occurrenceDegree f x-occurrenceDegree (fun e : {e // keep e}=>f e.val) x=
      ∑ e,if ¬keep e ∧ f e=x then (1:ℝ) else 0 := by
  rw [occurrenceDegree_restricted]
  unfold occurrenceDegree
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hk : keep e <;> by_cases hx : f e=x <;> simp [hk,hx]

theorem occurrenceDegree_restriction_change (f : E → V) (keep : E → Prop) (x : V) (d : ℝ)
    (hd : (∑ e,if ¬keep e ∧ f e=x then (1:ℝ) else 0)≤d) :
    |occurrenceDegree (fun e : {e // keep e}=>f e.val) x-occurrenceDegree f x|≤d := by
  have hn : 0≤occurrenceDegree f x-occurrenceDegree (fun e : {e // keep e}=>f e.val) x := by
    rw [occurrenceDegree_restriction_loss]
    exact Finset.sum_nonneg (fun e _=>by split_ifs <;> norm_num)
  rw [abs_sub_comm,abs_of_nonneg hn,occurrenceDegree_restriction_loss]
  exact hd

theorem occurrenceDegree_restriction_target (f : E → V) (keep : E → Prop) (x : V) (μ e d : ℝ)
    (hbase : |occurrenceDegree f x-μ|≤e)
    (hdel : (∑ a,if ¬keep a ∧ f a=x then (1:ℝ) else 0)≤d) :
    |occurrenceDegree (fun a : {a // keep a}=>f a.val) x-μ|≤e+d := by
  have hloss := occurrenceDegree_restriction_change f keep x d hdel
  have ht := abs_sub_le (occurrenceDegree (fun a : {a // keep a}=>f a.val) x) (occurrenceDegree f x) μ
  linarith

end Oberwolfach
