module

public import Oberwolfach.OrdinaryCycleCountBounds

@[expose] public section

/-! Restricting a weighted subfamily of a product to two specified events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem product_subtype_event_bound {A U : Type*} [Fintype A] [Fintype U] [DecidableEq U]
    (admissible : A×U → Prop) (w : {p // admissible p} → ℝ) (M : ℝ) (hM : 0≤M)
    (hw : ∀ p,w p≤M) (S : A → Prop) (T : Finset U)
    (P : {p // admissible p} → Prop) (hP : ∀ p,P p → S p.val.1 ∧ p.val.2∈T) :
    (∑ p,if P p then w p else 0)≤
      (T.card:ℝ)*(∑ a,if S a then M else 0) := by
  classical
  let g (p : A×U) : ℝ := if S p.1 ∧ p.2∈T then M else 0
  have hg (p : A×U) : 0≤g p := by dsimp only [g];split_ifs <;> positivity
  calc
    _ ≤ ∑ p : {p // admissible p},g p.val := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : P p
      · simp only [if_pos hp,g,if_pos (hP p hp)]
        exact hw p
      · rw [if_neg hp];exact hg p.val
    _ ≤ ∑ p : A×U,g p :=
      finite_injective_sum_le (fun p : {p // admissible p}=>p.val) Subtype.val_injective g hg
    _ = _ := by
      rw [Fintype.sum_prod_type,Finset.sum_comm]
      have he (u : U) : (∑ a : A,g (a,u))=
          if u∈T then (∑ a : A,if S a then M else 0) else 0 := by
        by_cases hu : u∈T
        · simp only [g,hu,and_true,ite_true]
        · simp only [g,hu,and_false,ite_false,Finset.sum_const_zero]
      simp only [he]
      rw [← Finset.sum_filter]
      have ht : Finset.univ.filter (fun u=>u∈T)=T := by ext;simp
      rw [ht,Finset.sum_const,nsmul_eq_mul]

end Oberwolfach
