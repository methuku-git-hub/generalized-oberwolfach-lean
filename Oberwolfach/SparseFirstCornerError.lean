module

public import Oberwolfach.SparseIntersectionData
public import Oberwolfach.SparseAlternatingOperator

@[expose] public section

/-! The first corner contribution is close to the original edge weight,
using the given column degree and weighted codegree estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem sparse_first_corner_error (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (h : SparseIntersectionData H p q L δ D)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B) (x : A) (u : B) :
    |q u/((Fintype.card A:ℝ)*Fintype.card B)*
      (∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-1|≤
      L*(2*δ+(L^2+1)*(D/(Fintype.card A:ℝ))) := by
  let a : ℝ := Fintype.card A
  let b : ℝ := Fintype.card B
  have ha' : 0<a := Nat.cast_pos.mpr ha
  have hb' : 0<b := Nat.cast_pos.mpr hb
  have hL := h.L_nonneg
  have hδ := h.delta_nonneg
  have hD := h.D_nonneg
  have hS := bipWeightedCodegree_error_sum H q L δ D hL hδ h.inverse_bounds
    h.exceptionalSets h.exceptionalSets_card h.exceptionalSets_error x
  have he : (∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-a*b*p u=
      (∑ y,bipAdj H y u*(bipWeightedCodegree H q x y-b))+b*(bipColumnDegree H u-a*p u) := by
    unfold bipColumnDegree
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]
    ring
  have hsum : |(∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-a*b*p u|≤
      a*δ*b+D*(L^2+1)*b+b*(δ*a) := by
    rw [he]
    calc
      _ ≤ |∑ y,bipAdj H y u*(bipWeightedCodegree H q x y-b)|+|b*(bipColumnDegree H u-a*p u)| := abs_add_le _ _
      _ ≤ (∑ y,|bipWeightedCodegree H q x y-b|)+b*(δ*a) := by
        apply add_le_add
        · have hh := weighted_sum_abs_le (fun y=>bipAdj H y u)
            (fun y=>bipWeightedCodegree H q x y-b) 1 (by norm_num)
            (fun y=>by rw [abs_of_nonneg (bipAdj_nonneg H y u)];exact bipAdj_le_one H y u)
          simpa only [one_mul] using hh
        · rw [abs_mul,abs_of_nonneg hb'.le]
          exact mul_le_mul_of_nonneg_left (h.degree_error u) hb'.le
      _ ≤ _ := add_le_add hS le_rfl
  have he' : q u/(a*b)*(∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-1=
      q u/(a*b)*((∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-a*b*p u) := by
    symm
    calc
      _ = q u/(a*b)*(∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-q u*p u := by field_simp <;> ring
      _ = _ := by rw [h.inverse_identity u]
  change |q u/(a*b)*(∑ y,bipAdj H y u*bipWeightedCodegree H q x y)-1|≤_
  rw [he',abs_mul,abs_of_nonneg (div_nonneg (h.inverse_bounds u).1 (by positivity))]
  calc
    _ ≤ (L/(a*b))*(a*δ*b+D*(L^2+1)*b+b*(δ*a)) := by
      exact mul_le_mul (div_le_div_of_nonneg_right (h.inverse_bounds u).2 (by positivity)) hsum
        (abs_nonneg _) (by positivity)
    _ = _ := by field_simp <;> ring

end Oberwolfach
