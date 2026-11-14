module

public import Oberwolfach.AlternatingRectangles

@[expose] public section

/-! Exact entry equations for finite linear combinations of alternating
rectangles. The entries are indexed by the actual two vertex classes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def rectangleCombination (f : A → A → B → B → ℝ) (e : A×B) : ℝ :=
  ∑ x,∑ y,∑ u,∑ v,f x y u v*alternatingRectangle x y u v e.1 e.2

theorem rectangleCombination_entry (f : A → A → B → B → ℝ) (x : A) (u : B) :
    rectangleCombination f (x,u)=
      ∑ y,∑ v,(f x y u v-f y x u v+f y x v u-f x y v u) := by
  unfold rectangleCombination alternatingRectangle
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib]
  simp only [mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  ring

theorem rectangleCombination_zero_marginals (H : A → B → Prop)
    (f : A → A → B → B → ℝ)
    (hf : ∀ x y u v, f x y u v≠0 → H x u ∧ H y u ∧ H y v ∧ H x v) :
    rectangleCombination f∈zeroMarginalSpace H := by
  refine ⟨?_,?_,?_⟩
  · intro a b hab
    unfold rectangleCombination
    apply Finset.sum_eq_zero;intro x _
    apply Finset.sum_eq_zero;intro y _
    apply Finset.sum_eq_zero;intro u _
    apply Finset.sum_eq_zero;intro v _
    by_cases h : f x y u v=0
    · rw [h,zero_mul]
    have hh := hf x y u v h
    unfold alternatingRectangle
    split_ifs <;> simp_all
  · intro a
    unfold rectangleCombination
    simp only [Finset.sum_comm (f:=fun b x => ∑ y,∑ u,∑ v,
      f x y u v*alternatingRectangle x y u v a b)]
    apply Finset.sum_eq_zero;intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero;intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero;intro u _
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,alternatingRectangle_row_sum,mul_zero,Finset.sum_const_zero]
  · intro b
    unfold rectangleCombination
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero;intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero;intro y _
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero;intro u _
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,alternatingRectangle_column_sum,mul_zero,Finset.sum_const_zero]

end Oberwolfach
