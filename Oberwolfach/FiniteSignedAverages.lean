module

public import Oberwolfach.FractionalDecompositions

@[expose] public section

/-! Finite averages of signed coefficient vectors, including exact linear
tests and absolute coefficient bounds. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def finiteSignedAverage {I W : Type*} [Fintype I] (a : I → W → ℝ) (w : W) : ℝ :=
  (∑ i,a i w)/(Fintype.card I:ℝ)

theorem finiteSignedAverage_test {I W : Type*} [Fintype I] [Fintype W]
    (a : I → W → ℝ) (t : W → ℝ) :
    (∑ w,finiteSignedAverage a w*t w)=
      (∑ i,∑ w,a i w*t w)/(Fintype.card I:ℝ) := by
  unfold finiteSignedAverage
  calc
    _ = ∑ w,∑ i,(a i w*t w)/(Fintype.card I:ℝ) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_div,← Finset.sum_mul]
      ring
    _ = ∑ i,∑ w,(a i w*t w)/(Fintype.card I:ℝ) := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_div]

theorem finiteSignedAverage_constant_test {I W : Type*} [Fintype I] [Fintype W]
    (hI : 0<Fintype.card I) (a : I → W → ℝ) (t : W → ℝ) (K : ℝ)
    (ht : ∀ i,(∑ w,a i w*t w)=K) :
    (∑ w,finiteSignedAverage a w*t w)=K := by
  rw [finiteSignedAverage_test]
  simp only [ht,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hh : (Fintype.card I:ℝ)≠0 := (Nat.cast_pos.mpr hI).ne'
  field_simp

theorem finiteSignedAverage_abs_le {I W : Type*} [Fintype I]
    (a : I → W → ℝ) (w : W) :
    |finiteSignedAverage a w|≤(∑ i,|a i w|)/(Fintype.card I:ℝ) := by
  unfold finiteSignedAverage
  rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

theorem finiteSignedAverage_eq_zero {I W : Type*} [Fintype I]
    (a : I → W → ℝ) (w : W) (hw : ∀ i,a i w=0) : finiteSignedAverage a w=0 := by
  simp only [finiteSignedAverage,hw,Finset.sum_const_zero,zero_div]

theorem finiteSignedAverage_indicator_constant {I W : Type*} [Fintype I] [Fintype W]
    (hI : 0<Fintype.card I) (a : I → W → ℝ) (P : W → Prop) (K : ℝ)
    (ht : ∀ i,(∑ w,if P w then a i w else 0)=K) :
    (∑ w,if P w then finiteSignedAverage a w else 0)=K := by
  classical
  have hh := finiteSignedAverage_constant_test hI a (fun w => if P w then (1:ℝ) else 0) K
    (fun i => by simpa only [mul_ite,mul_one,mul_zero] using ht i)
  simpa only [mul_ite,mul_one,mul_zero] using hh

end Oberwolfach
