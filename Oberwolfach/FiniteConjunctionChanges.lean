module

public import Oberwolfach.RootedPatternStability

@[expose] public section

/-! Changes of a finite conjunction are charged to the predicates that
actually change. A fixed admissibility condition is kept in both counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteConjunction_sum_change {X I : Type*} (A : Finset X) (J : Finset I)
    (F : X→Prop) (P Q : I→X→Prop) :
    |(∑ x∈A,if F x ∧ ∀ j∈J,Q j x then (1:ℝ) else 0)-
      (∑ x∈A,if F x ∧ ∀ j∈J,P j x then (1:ℝ) else 0)|≤
      ∑ j∈J,∑ x∈A,if ¬(P j x ↔ Q j x) then (1:ℝ) else 0 := by
  classical
  have hp (x : X) :
      |(if F x ∧ ∀ j∈J,Q j x then (1:ℝ) else 0)-
        (if F x ∧ ∀ j∈J,P j x then (1:ℝ) else 0)|≤
        ∑ j∈J,if ¬(P j x ↔ Q j x) then (1:ℝ) else 0 := by
    by_cases he : ∃ j∈J,¬(P j x ↔ Q j x)
    · obtain ⟨j,hj,hchange⟩ := he
      have hsum := Finset.single_le_sum (s:=J)
        (f:=fun j=>if ¬(P j x ↔ Q j x) then (1:ℝ) else 0)
        (fun _ _=>by split_ifs <;> norm_num) hj
      rw [if_pos hchange] at hsum
      apply le_trans (b:=1) ?_ hsum
      split_ifs <;> norm_num
    · have heq : (F x ∧ ∀ j∈J,P j x) ↔ (F x ∧ ∀ j∈J,Q j x) := by
        have hj : ∀ j∈J,P j x ↔ Q j x := by
          intro j hj
          by_contra hh
          exact he ⟨j,hj,hh⟩
        exact and_congr_right (fun _=>forall_congr' (fun j=>forall_congr' (fun h=>hj j h)))
      simp only [heq,sub_self,abs_zero]
      exact Finset.sum_nonneg (fun _ _=>by split_ifs <;> norm_num)

  calc
    _ ≤ ∑ x∈A,|(if F x ∧ ∀ j∈J,Q j x then (1:ℝ) else 0)-
          (if F x ∧ ∀ j∈J,P j x then (1:ℝ) else 0)| := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x∈A,∑ j∈J,if ¬(P j x ↔ Q j x) then (1:ℝ) else 0 :=
      Finset.sum_le_sum (fun x _=>hp x)
    _ = _ := Finset.sum_comm

theorem finiteConjunction_sum_change_at_outer {X I : Type*} (A C : Finset X) (hCA : C⊆A)
    (J : Finset I) (F : X→Prop) (P Q : I→X→Prop) (δ : ℝ)
    (h : ∀ j∈J,(∑ x∈A,if ¬(P j x ↔ Q j x) then (1:ℝ) else 0)≤δ) :
    |(∑ x∈C,if F x ∧ ∀ j∈J,Q j x then (1:ℝ) else 0)-
      (∑ x∈C,if F x ∧ ∀ j∈J,P j x then (1:ℝ) else 0)|≤J.card*δ := by
  apply (finiteConjunction_sum_change C J F P Q).trans
  calc
    _ ≤ ∑ j∈J,δ := Finset.sum_le_sum (fun j hj=>
      (Finset.sum_le_sum_of_subset_of_nonneg hCA (by intro x hx hn;split_ifs <;> norm_num)).trans (h j hj))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

end Oberwolfach
