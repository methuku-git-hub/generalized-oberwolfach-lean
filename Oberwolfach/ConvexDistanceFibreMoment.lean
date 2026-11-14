module

public import Oberwolfach.FiniteExponentialInterpolation
public import Oberwolfach.ConvexDistanceScalar

@[expose] public section

/-! The exponential-moment estimate for one fibre in the product-space
induction. The probabilities of the fibre and its projection remain
explicit throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {Ω : Type*} [Fintype Ω]

theorem finiteLaw_shifted_exponential_interpolation
    (μ : FiniteLaw Ω) (X Y Z : Ω → ℝ) {a b c θ : ℝ}
    (hθ0 : 0≤θ) (hθ1 : θ≤1)
    (hX : μ.expectation (fun ω=>Real.exp (X ω))≤Real.exp a)
    (hY : μ.expectation (fun ω=>Real.exp (Y ω))≤Real.exp b)
    (hZ : ∀ ω,Z ω≤θ*X ω+(1-θ)*Y ω+c) :
    μ.expectation (fun ω=>Real.exp (Z ω))≤Real.exp (c+θ*a+(1-θ)*b) := by
  have hh := finiteLaw_exponential_interpolation μ X Y hθ0 hθ1 hX hY
  calc
    _ ≤ μ.expectation (fun ω=>Real.exp c*Real.exp (θ*X ω+(1-θ)*Y ω)) := by
      apply finiteLaw_expectation_mono
      intro ω
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hZ ω]
    _ = Real.exp c*μ.expectation (fun ω=>Real.exp (θ*X ω+(1-θ)*Y ω)) :=
      finiteLaw_expectation_const_mul _ _ _
    _ ≤ Real.exp c*Real.exp (θ*a+(1-θ)*b) :=
      mul_le_mul_of_nonneg_left hh (Real.exp_pos c).le
    _ = _ := by rw [← Real.exp_add];congr 1;ring

theorem finiteLaw_convexDistance_fibre_moment
    (μ : FiniteLaw Ω) (X Y Z : Ω → ℝ) {a b : ℝ}
    (ha : 0<a) (hab : a≤b)
    (hX : μ.expectation (fun ω=>Real.exp (X ω))≤a⁻¹)
    (hY : μ.expectation (fun ω=>Real.exp (Y ω))≤b⁻¹)
    (hZ : ∀ θ : ℝ,0≤θ → θ≤1 →
      ∀ ω,Z ω≤θ*X ω+(1-θ)*Y ω+(1-θ)^2/4) :
    μ.expectation (fun ω=>Real.exp (Z ω))≤(2-a/b)/b := by
  have hb : 0<b := ha.trans_le hab
  have hr : 0<a/b := div_pos ha hb
  obtain ⟨θ,hθ0,hθ1,_,hscalar⟩ :=
    convexDistance_scalar_choice hr.le ((div_le_one hb).mpr hab)
  have hXa : μ.expectation (fun ω=>Real.exp (X ω))≤Real.exp (-Real.log a) := by
    rwa [Real.exp_neg,Real.exp_log ha]
  have hYb : μ.expectation (fun ω=>Real.exp (Y ω))≤Real.exp (-Real.log b) := by
    rwa [Real.exp_neg,Real.exp_log hb]
  have hh := finiteLaw_shifted_exponential_interpolation μ X Y Z hθ0 hθ1 hXa hYb
    (hZ θ hθ0 hθ1)
  have he : Real.exp ((1-θ)^2/4+θ*(-Real.log a)+(1-θ)*(-Real.log b))=
      (Real.exp ((1-θ)^2/4)*(a/b)^(-θ))/b := by
    rw [Real.rpow_def_of_pos hr,Real.log_div ha.ne' hb.ne']
    have hexp : (1-θ)^2/4+θ*(-Real.log a)+(1-θ)*(-Real.log b)=
        ((1-θ)^2/4+(Real.log a-Real.log b)*(-θ))-Real.log b := by ring
    rw [hexp,Real.exp_sub,Real.exp_add,Real.exp_log hb]
  rw [he] at hh
  exact hh.trans (div_le_div_of_nonneg_right hscalar hb.le)

theorem finiteLaw_convexDistance_empty_fibre_moment
    (μ : FiniteLaw Ω) (Y Z : Ω → ℝ) {b : ℝ} (hb : 0<b)
    (hY : μ.expectation (fun ω=>Real.exp (Y ω))≤b⁻¹)
    (hZ : ∀ ω,Z ω≤Y ω+1/4) :
    μ.expectation (fun ω=>Real.exp (Z ω))≤2/b := by
  have he : Real.exp (1/4 : ℝ)≤2 := by
    have hh := Real.exp_bound_div_one_sub_of_interval (x:=(1/4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at hh
    linarith
  calc
    _ ≤ μ.expectation (fun ω=>Real.exp (1/4 : ℝ)*Real.exp (Y ω)) := by
      apply finiteLaw_expectation_mono
      intro ω
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hZ ω])
    _ = Real.exp (1/4 : ℝ)*μ.expectation (fun ω=>Real.exp (Y ω)) :=
      finiteLaw_expectation_const_mul _ _ _
    _ ≤ Real.exp (1/4 : ℝ)*b⁻¹ :=
      mul_le_mul_of_nonneg_left hY (Real.exp_pos _).le
    _ ≤ 2/b := by simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hb.le)

end Oberwolfach
