module

public import Oberwolfach.MatchingIntegerScales
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-! Scalar estimates for the three common events in weighted matching.
The estimates apply to the original weight functions; no random normalisation
or outcome-dependent test family is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem matching_exp_quadratic {x : ℝ} (hx : 0≤x) (hx1 : x≤1) :
    Real.exp x≤1+x+x^2 := by
  have hh := Real.exp_bound' hx hx1 (n:=2) (by norm_num)
  norm_num [Finset.sum_range_succ] at hh
  nlinarith [sq_nonneg x]

theorem matching_degree_exponent {η h μ d : ℝ} (hη : 0<η) (hη1 : η≤1/100)
    (_hh : 0≤h) (hμ : μ≤(1+3*η)*h^4) (hd : (1+4*η)*h^4≤d) :
    μ*(Real.exp (η/4)-1)-(η/4)*(d+1)≤-η^2*h^4/8 := by
  have he := matching_exp_quadratic (show 0≤η/4 by positivity) (show η/4≤1 by linarith)
  have hep : 0≤Real.exp (η/4)-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have hm := mul_le_mul_of_nonneg_right hμ hep
  have he' := mul_le_mul_of_nonneg_left (show Real.exp (η/4)-1≤η/4+(η/4)^2 by linarith)
    (show 0≤(1+3*η)*h^4 by positivity)
  have hd' := mul_le_mul_of_nonneg_left hd (show 0≤η/4 by positivity)
  have hηsq : 3*η^3≤η^2 := by nlinarith [sq_nonneg η]
  have hc := mul_le_mul_of_nonneg_right hηsq (show 0≤h^4 by positivity)
  nlinarith

theorem matching_codegree_exponent {h μ : ℝ} (hh : 2≤h) (hμ : μ≤1) :
    μ*(Real.exp 1-1)-(h+1)≤-h/2 := by
  have hep : 0≤Real.exp 1-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hm := mul_le_mul_of_nonneg_right hμ hep
  have he := Real.exp_one_lt_three
  nlinarith

theorem matching_weight_exponent {η z μ b : ℝ} (hη : 0≤η) (hη1 : η≤1/100)
    (hz : 0≤z) (hb : 0<b) (hμ : μ≤(1+η)*z) :
    (μ*(Real.exp (1/4)-1)-(1/4)*(2*z))/b≤-z/(8*b) := by
  have he := matching_exp_quadratic (show (0 : ℝ)≤1/4 by norm_num) (show (1 : ℝ)/4≤1 by norm_num)
  have hep : 0≤Real.exp (1/4)-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  have hm := mul_le_mul_of_nonneg_right hμ hep
  have he' := mul_le_mul_of_nonneg_left (show Real.exp (1/4)-1≤5/16 by linarith)
    (show 0≤(1+η)*z by positivity)
  have hηz := mul_le_mul_of_nonneg_right hη1 hz
  apply (div_le_iff₀ hb).mpr
  field_simp
  nlinarith

theorem matching_normalization_error {x W D E η : ℝ}
    (hW : 0≤W) (hD : 0<D) (hη : 0≤η) (hDE : D≤E) (hED : E≤(1+8*η)*D)
    (hx : |x-W/E|<η*W/D+η*W/E) :
    |x-W/D|<10*η*W/D := by
  have hE : 0<E := hD.trans_le hDE
  have hdiv : W/E≤W/D := div_le_div_of_nonneg_left hW hD hDE
  have hdiff : W/D-W/E≤8*η*W/D := by
    apply (le_div_iff₀ hD).mpr
    have haux : E-D≤8*η*E := by nlinarith
    have hm := mul_le_mul_of_nonneg_left haux hW
    apply (mul_le_mul_iff_of_pos_right hE).mp
    field_simp
    nlinarith
  calc
    _ ≤ |x-W/E|+|W/E-W/D| := by convert abs_add_le (x-W/E) (W/E-W/D) using 1 <;> ring
    _ < (η*W/D+η*W/E)+8*η*W/D := add_lt_add_of_lt_of_le hx (by rw [abs_of_nonpos (by linarith)];linarith)
    _ ≤ 10*η*W/D := by
      have hm := mul_le_mul_of_nonneg_left hdiv hη
      simp only [← mul_div_assoc] at hm
      convert add_le_add_right (add_le_add_left hm (η*W/D)) (8*η*W/D) using 1 <;> ring

end Oberwolfach
