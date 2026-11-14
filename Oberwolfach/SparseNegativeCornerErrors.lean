module

public import Oberwolfach.SparseIntersectionData
public import Oberwolfach.SparseAlternatingOperator

@[expose] public section

/-! Cancellation of the two negative corner contributions using the
actual zero column and zero row equations. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem sparse_second_corner_error (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (h : SparseIntersectionData H p q L δ D)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B)
    (z : A×B → ℝ) (hcol : ∀ u,∑ y,z (y,u)=0) (x : A) (u : B) :
    |q u/((Fintype.card A:ℝ)*Fintype.card B)*(∑ y,z (y,u)*bipWeightedCodegree H q x y)|≤
      L*(δ+(L^2+1)*(D/(Fintype.card A:ℝ)))*‖z‖ := by
  let a : ℝ := Fintype.card A
  let b : ℝ := Fintype.card B
  have ha' : 0<a := Nat.cast_pos.mpr ha
  have hb' : 0<b := Nat.cast_pos.mpr hb
  have hL := h.L_nonneg
  have hδ := h.delta_nonneg
  have hD := h.D_nonneg
  have hS := bipWeightedCodegree_error_sum H q L δ D hL hδ h.inverse_bounds
    h.exceptionalSets h.exceptionalSets_card h.exceptionalSets_error x
  have hz (y : A) : |z (y,u)|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z (y,u)
  have hsum : |∑ y,z (y,u)*bipWeightedCodegree H q x y|≤‖z‖*(a*δ*b+D*(L^2+1)*b) :=
    (sum_absolute_difference_cancel (fun y=>z (y,u)) (fun y=>bipWeightedCodegree H q x y)
      b ‖z‖ (hcol u) (norm_nonneg _) hz).trans
      (mul_le_mul_of_nonneg_left hS (norm_nonneg _))
  change |q u/(a*b)*(∑ y,z (y,u)*bipWeightedCodegree H q x y)|≤_
  rw [abs_mul,abs_of_nonneg (div_nonneg (h.inverse_bounds u).1 (by positivity))]
  calc
    _ ≤ (L/(a*b))*(‖z‖*(a*δ*b+D*(L^2+1)*b)) :=
      mul_le_mul (div_le_div_of_nonneg_right (h.inverse_bounds u).2 (by positivity)) hsum
        (abs_nonneg _) (by positivity)
    _ = _ := by field_simp <;> ring

theorem sparse_fourth_corner_error (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (h : SparseIntersectionData H p q L δ D)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B)
    (z : A×B → ℝ) (hrow : ∀ x,∑ v,z (x,v)=0) (x : A) (u : B) :
    |(q u)^2/((Fintype.card A:ℝ)*Fintype.card B)*
      (∑ v,z (x,v)*q v*bipPairIntersection H v u)|≤
        L^3*(δ+2/(Fintype.card B:ℝ))*‖z‖ := by
  let a : ℝ := Fintype.card A
  let b : ℝ := Fintype.card B
  have ha' : 0<a := Nat.cast_pos.mpr ha
  have hb' : 0<b := Nat.cast_pos.mpr hb
  have hL := h.L_nonneg
  have hδ := h.delta_nonneg
  have hbase : (∑ v,z (x,v)*q v*(a*p v*p u))=0 := by
    calc
      _ = a*p u*(∑ v,z (x,v)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl;intro v _
        calc
          _ = a*p u*z (x,v)*(q v*p v) := by ring
          _ = _ := by rw [h.inverse_identity v];ring
      _ = _ := by rw [hrow x,mul_zero]
  have he : (∑ v,z (x,v)*q v*bipPairIntersection H v u)=
      ∑ v,z (x,v)*q v*(bipPairIntersection H v u-a*p v*p u) := by
    simp only [mul_sub,Finset.sum_sub_distrib,hbase,sub_zero]
  have hz (v : B) : |z (x,v)*q v|≤L*‖z‖ := by
    rw [abs_mul,abs_of_nonneg (h.inverse_bounds v).1]
    have hbz : |z (x,v)|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z (x,v)
    calc
      _ ≤ ‖z‖*L := mul_le_mul hbz (h.inverse_bounds v).2 (h.inverse_bounds v).1 (norm_nonneg _)
      _ = _ := by ring
  have hsum : |∑ v,z (x,v)*q v*bipPairIntersection H v u|≤L*‖z‖*(b*δ*a+2*a) := by
    rw [he]
    exact (weighted_sum_abs_le _ _ (L*‖z‖) (by positivity) hz).trans
      (mul_le_mul_of_nonneg_left (bipPairIntersection_error_sum H p h.density δ hδ h.pair_error u) (by positivity))
  change |(q u)^2/(a*b)*(∑ v,z (x,v)*q v*bipPairIntersection H v u)|≤_
  rw [abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
  calc
    _ ≤ (L^2/(a*b))*(L*‖z‖*(b*δ*a+2*a)) :=
      mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ (h.inverse_bounds u).1 (h.inverse_bounds u).2 2) (by positivity))
        hsum (abs_nonneg _) (by positivity)
    _ = _ := by field_simp <;> ring

end Oberwolfach
