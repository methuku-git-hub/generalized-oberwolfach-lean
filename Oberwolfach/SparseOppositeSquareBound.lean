module

public import Oberwolfach.SparseIntersectionData
public import Oberwolfach.TripleKernelErrorSum

@[expose] public section

/-! The square of the opposite-corner operator is small on vectors with
zero row sums. The input need not be changed or renormalized. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem sparseOppositeMap_square_norm (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (h : SparseIntersectionData H p q L δ D)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B)
    (z : A×B → ℝ) (hz : ∀ s,∑ t,z (s,t)=0) :
    ‖sparseOppositeMap H q (sparseOppositeMap H q z)‖≤
      8*L^6*(δ+D/(Fintype.card A:ℝ)+1/(Fintype.card B:ℝ))*‖z‖ := by
  let a : ℝ := Fintype.card A
  let b : ℝ := Fintype.card B
  have ha' : 0<a := Nat.cast_pos.mpr ha
  have hb' : 0<b := Nat.cast_pos.mpr hb
  have hL := h.L_nonneg
  have hδ := h.delta_nonneg
  have hD := h.D_nonneg
  let R := (L^3+1)*δ+(L^3+1)*(D/a)+(5*L^3+1)/b
  have hR : 0≤R := by dsimp [R];positivity
  have hscalar : L^3*R≤8*L^6*(δ+D/a+1/b) := by
    simpa only [R,mul_div,mul_one] using sparse_second_error_scalar L δ (D/a) (1/b)
      h.one_le_L hδ (by positivity) (by positivity)
  apply (pi_norm_le_iff_of_nonneg (show 0≤8*L^6*(δ+D/a+1/b)*‖z‖ by positivity)).mpr
  intro e
  rcases e with ⟨x,u⟩
  have hFsum : (∑ s,∑ t,|bipTripleKernel H q x u s t-a*b*p u*p t|)≤a^2*b^2*R := by
    have hh := bipTripleKernel_error_sum H p q L δ D hL hδ hD h.density h.inverse_bounds
      h.inverse_identity h.triple_error h.exceptionalSets h.exceptionalSets_card h.exceptionalSets_error x u
    calc
      _ ≤ b*(a*(L^3*(b*δ*a+4*a)+a*δ*b)+D*((L^3+1)*a*b))+a*((L^3+1)*a*b) := hh
      _ = _ := by dsimp only [R];field_simp <;> ring
  have hbase : (∑ s,∑ t,z (s,t)*q t*(a*b*p u*p t))=0 := by
    calc
      _ = a*b*p u*(∑ s,∑ t,z (s,t)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl;intro s _
        apply Finset.sum_congr rfl;intro t _
        calc
          _ = a*b*p u*z (s,t)*(q t*p t) := by ring
          _ = _ := by rw [h.inverse_identity t];ring
      _ = _ := by simp only [hz,Finset.sum_const_zero,mul_zero]
  have he : (∑ s,∑ t,z (s,t)*q t*bipTripleKernel H q x u s t)=
      ∑ s,∑ t,z (s,t)*q t*(bipTripleKernel H q x u s t-a*b*p u*p t) := by
    simp only [mul_sub,Finset.sum_sub_distrib,hbase,sub_zero]
  have hweight (e : A×B) : |z e*q e.2|≤L*‖z‖ := by
    rw [abs_mul,abs_of_nonneg (h.inverse_bounds e.2).1]
    have hn : |z e|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z e
    calc
      _ ≤ ‖z‖*L := mul_le_mul hn (h.inverse_bounds e.2).2 (h.inverse_bounds e.2).1 (norm_nonneg _)
      _ = _ := by ring
  have hsum : |∑ s,∑ t,z (s,t)*q t*bipTripleKernel H q x u s t|≤L*‖z‖*(a^2*b^2*R) := by
    rw [he]
    have hh := weighted_sum_abs_le (fun e : A×B=>z e*q e.2)
      (fun e : A×B=>bipTripleKernel H q x u e.1 e.2-a*b*p u*p e.2)
      (L*‖z‖) (by positivity) hweight
    simp only [Fintype.sum_prod_type] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hFsum (by positivity))
  have hc : 0≤bipAdj H x u*(q u)^2/(a^2*b^2) := by
    exact div_nonneg (mul_nonneg (bipAdj_nonneg H x u) (sq_nonneg _)) (by positivity)
  have hcoef : bipAdj H x u*(q u)^2/(a^2*b^2)≤L^2/(a^2*b^2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ 1*L^2 := mul_le_mul (bipAdj_le_one H x u)
        (pow_le_pow_left₀ (h.inverse_bounds u).1 (h.inverse_bounds u).2 2) (sq_nonneg _) (by norm_num)
      _ = _ := one_mul _
  rw [Real.norm_eq_abs,sparseOppositeMap_square]
  change |bipAdj H x u*(q u)^2/(a^2*b^2)*(∑ s,∑ t,z (s,t)*q t*bipTripleKernel H q x u s t)|≤_
  rw [abs_mul,abs_of_nonneg hc]
  calc
    _ ≤ (L^2/(a^2*b^2))*(L*‖z‖*(a^2*b^2*R)) :=
      mul_le_mul hcoef hsum (abs_nonneg _) (by positivity)
    _ = L^3*R*‖z‖ := by field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)

end Oberwolfach
