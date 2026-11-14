module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section

/-! Finite sums with explicitly identified exceptional indices. -/
set_option autoImplicit false
open scoped BigOperators
namespace Oberwolfach

theorem exceptional_sum_abs_le {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℝ) (E : Finset I) (e M : ℝ) (he : 0≤e) (hM : 0≤M)
    (hgood : ∀ i,i∉E → |f i|≤e) (hall : ∀ i,|f i|≤M) :
    (∑ i,|f i|)≤(Fintype.card I:ℝ)*e+(E.card:ℝ)*M := by
  calc
    _ ≤ ∑ i,(e+if i∈E then M else 0) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i∈E
      · simp only [hi,ite_true];linarith [hall i]
      · simp only [hi,ite_false,add_zero];exact hgood i hi
    _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_ite_mem,nsmul_eq_mul]

theorem weighted_sum_abs_le {I : Type*} [Fintype I]
    (f g : I → ℝ) (M : ℝ) (hM : 0≤M) (hf : ∀ i,|f i|≤M) :
    |∑ i,f i*g i|≤M*(∑ i,|g i|) := by
  calc
    _ ≤ ∑ i,|f i*g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,M*|g i| := by
      apply Finset.sum_le_sum;intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem sum_absolute_difference_cancel {I : Type*} [Fintype I]
    (f g : I → ℝ) (c M : ℝ) (hf : ∑ i,f i=0) (hM : 0≤M)
    (hbound : ∀ i,|f i|≤M) :
    |∑ i,f i*g i|≤M*(∑ i,|g i-c|) := by
  have he : (∑ i,f i*g i)=(∑ i,f i*(g i-c)) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hf,zero_mul,sub_zero]
  rw [he]
  exact weighted_sum_abs_le f (fun i=>g i-c) M hM hbound

end Oberwolfach
