module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section

/-! Squared influence for fixed nonnegative pattern sums, bounded through
actual resource incidences and total coefficient. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_pattern_incidence_square_sum {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I]
    (R : I → Finset A) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (a q L : ℝ) (ha : 0≤a) (hq : 0≤q)
    (hsize : ∀ i,((R i).card:ℝ)≤q) (htotal : (∑ i,w i)≤L)
    (hload : ∀ e,(∑ i,if e∈R i then w i else 0)≤a) :
    (∑ e,(∑ i,if e∈R i then w i else 0)^2)≤a*q*L := by
  have hnonneg (e : A) : (0:ℝ)≤∑ i,if e∈R i then w i else 0 := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs;exact hw i;exact le_refl _
  have hsum : (∑ e,∑ i,if e∈R i then w i else 0)≤q*L := by
    rw [Finset.sum_comm]
    have he (i : I) : (∑ e,if e∈R i then w i else 0)=((R i).card:ℝ)*w i := by
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun e=>e∈R i)=R i := by ext e;simp
      rw [he,Finset.sum_const,nsmul_eq_mul]
    simp_rw [he]
    calc
      _ ≤ ∑ i,q*w i := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (hsize i) (hw i))
      _ = q*∑ i,w i := (Finset.mul_sum _ _ _).symm
      _ ≤ q*L := mul_le_mul_of_nonneg_left htotal hq
  calc
    _ ≤ ∑ e,a*(∑ i,if e∈R i then w i else 0) := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hload e) (hnonneg e)
    _ = a*(∑ e,∑ i,if e∈R i then w i else 0) := (Finset.mul_sum _ _ _).symm
    _ ≤ a*(q*L) := mul_le_mul_of_nonneg_left hsum ha
    _ = _ := by ring

end Oberwolfach
