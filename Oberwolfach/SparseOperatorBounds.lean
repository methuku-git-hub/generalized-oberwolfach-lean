module

public import Oberwolfach.SparseAlternatingOperator
public import Oberwolfach.AlternatingCoefficientLoads

@[expose] public section

/-! Norm and coefficient bounds for the concrete averaging operators. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem sparseRectangleCoefficient_bound (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ)
    (L : ℝ) (hL : 0≤L) (hq : ∀ u,0≤q u ∧ q u≤L) (x y : A) (u v : B) :
    |sparseRectangleCoefficient H q z x y u v|≤
      L^3*‖z‖/((Fintype.card A:ℝ)*Fintype.card B) := by
  have hz : |z (x,u)|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z (x,u)
  have hq0 := (hq u).1
  have hq1 := (hq v).1
  have hp : q u*(q v)^2≤L^3 := by
    calc
      _ ≤ L*L^2 := mul_le_mul (hq u).2 (pow_le_pow_left₀ hq1 (hq v).2 2) (sq_nonneg _) hL
      _ = _ := by ring
  unfold sparseRectangleCoefficient bipAdj
  split_ifs <;> simp only [one_mul,mul_one,zero_mul,mul_zero,zero_div,abs_zero]
  all_goals first
  | positivity
  | simp only [abs_div,abs_mul,abs_of_nonneg hq0,abs_of_nonneg (sq_nonneg (q v)),
        abs_of_nonneg (show (0:ℝ)≤(Fintype.card A:ℝ)*Fintype.card B by positivity)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ = |z (x,u)| *(q u*(q v)^2) := by ring
      _ ≤ ‖z‖*L^3 := mul_le_mul hz hp (by positivity) (norm_nonneg _)
      _ = _ := by ring

theorem sparseAlternating_coefficient_load (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ)
    (L : ℝ) (hL : 0≤L) (hq : ∀ u,0≤q u ∧ q u≤L)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B) (e : A×B) :
    (∑ Q : BipartiteFourCycle H,
      |sparseRectangleCoefficient H q z Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2| *
        |bipartiteFourCycleVector Q e|)≤4*L^3*‖z‖ := by
  have ha' : (0:ℝ)<Fintype.card A := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ)<Fintype.card B := Nat.cast_pos.mpr hb
  have hh := fourCycle_absolute_load H (sparseRectangleCoefficient H q z)
    (L^3*‖z‖/((Fintype.card A:ℝ)*Fintype.card B)) (by positivity)
    (sparseRectangleCoefficient_bound H q z L hL hq) e
  convert hh using 1 <;> field_simp <;> ring

theorem sparseOppositeMap_norm (H : A → B → Prop) (q : B → ℝ) (z : A×B → ℝ)
    (L : ℝ) (hL : 0≤L) (hq : ∀ u,0≤q u ∧ q u≤L)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B) :
    ‖sparseOppositeMap H q z‖≤L^3*‖z‖ := by
  have ha' : (0:ℝ)<Fintype.card A := Nat.cast_pos.mpr ha
  have hb' : (0:ℝ)<Fintype.card B := Nat.cast_pos.mpr hb
  apply (pi_norm_le_iff_of_nonneg (show 0≤L^3*‖z‖ by positivity)).mpr
  intro e
  rcases e with ⟨x,u⟩
  have hq0 := (hq u).1
  have hsum : |∑ y,∑ v,bipAdj H x v*bipAdj H y u*q v*z (y,v)|≤
      (Fintype.card A:ℝ)*(Fintype.card B:ℝ)*(L*‖z‖) := by
    calc
      _ ≤ ∑ y,|∑ v,bipAdj H x v*bipAdj H y u*q v*z (y,v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y,∑ v,|bipAdj H x v*bipAdj H y u*q v*z (y,v)| := by
        apply Finset.sum_le_sum;intro y _;exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y : A,∑ _v : B,L*‖z‖ := by
        apply Finset.sum_le_sum;intro y _
        apply Finset.sum_le_sum;intro v _
        have hqv := (hq v).1
        have hz : |z (y,v)|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z (y,v)
        unfold bipAdj
        split_ifs <;> simp only [one_mul,zero_mul,abs_zero]
        all_goals first
        | positivity
        | rw [abs_mul,abs_of_nonneg hqv]
          exact mul_le_mul (hq v).2 hz (abs_nonneg _) hL
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring
  change |bipAdj H x u*(q u)^2/((Fintype.card A:ℝ)*Fintype.card B)*
    (∑ y,∑ v,bipAdj H x v*bipAdj H y u*q v*z (y,v))|≤_
  have hcoef : 0≤bipAdj H x u*(q u)^2/((Fintype.card A:ℝ)*Fintype.card B) := by
    exact div_nonneg (mul_nonneg (bipAdj_nonneg H x u) (sq_nonneg _)) (by positivity)
  rw [abs_mul,abs_of_nonneg hcoef]
  calc
    _ ≤ (L^2/((Fintype.card A:ℝ)*Fintype.card B))*
        ((Fintype.card A:ℝ)*(Fintype.card B:ℝ)*(L*‖z‖)) := by
      apply mul_le_mul _ hsum (abs_nonneg _) (by positivity)
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ ≤ 1*L^2 := mul_le_mul (bipAdj_le_one H x u)
          (pow_le_pow_left₀ hq0 (hq u).2 2) (sq_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = _ := by field_simp <;> ring

end Oberwolfach
