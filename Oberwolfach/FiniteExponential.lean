module

public import Oberwolfach.UniformExposure
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-! Exponential moments and Chernoff's exponential Markov bound for finite laws. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Oberwolfach

theorem exp_mul_unit_interval {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    Real.exp (s * x) ≤ 1 + x * (Real.exp s - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ s)
    (sub_nonneg.mpr hx.2) hx.1 (show 1 - x + x = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  calc
    _ = Real.exp (x * s) := by rw [mul_comm]
    _ ≤ 1 - x + x * Real.exp s := h
    _ = _ := by ring

theorem finiteLaw_unit_interval_mgf
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hx : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    μ.expectation (fun ω => Real.exp (s * X ω)) ≤
      Real.exp (μ.expectation X * (Real.exp s - 1)) := by
  calc
    _ ≤ μ.expectation (fun ω => 1 + X ω * (Real.exp s - 1)) :=
      finiteLaw_expectation_mono μ _ _ (fun ω => exp_mul_unit_interval (hx ω) s)
    _ = 1 + μ.expectation X * (Real.exp s - 1) := by
      simp only [FiniteLaw.expectation, mul_add, mul_one, Finset.sum_add_distrib,
        μ.total, ← mul_assoc, Finset.sum_mul]
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (μ.expectation X * (Real.exp s - 1))

theorem finiteLaw_pi_expectation_product
    {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (X : ∀ i, Ω i → ℝ) :
    (FiniteLaw.pi μ).expectation (fun σ => ∏ i, X i (σ i)) = ∏ i, (μ i).expectation (X i) := by
  simp only [FiniteLaw.expectation, FiniteLaw.pi, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).mass x * X i x)).symm

theorem finiteLaw_independent_unit_interval_mgf
    {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hx : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    (FiniteLaw.pi μ).expectation (fun σ => Real.exp (s * ∑ i, X i (σ i))) ≤
      Real.exp ((∑ i, (μ i).expectation (X i)) * (Real.exp s - 1)) := by
  simp only [Finset.mul_sum, Real.exp_sum]
  rw [finiteLaw_pi_expectation_product μ (fun i x => Real.exp (s * X i x))]
  calc
    _ ≤ ∏ i, Real.exp ((μ i).expectation (X i) * (Real.exp s - 1)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun ω _ => mul_nonneg ((μ i).nonneg ω) (Real.exp_pos _).le)
      · intro i _
        exact finiteLaw_unit_interval_mgf (μ i) (X i) (hx i) s
    _ = _ := by rw [← Real.exp_sum, Finset.sum_mul]

theorem finiteLaw_exponential_markov
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.probability (fun ω => a ≤ X ω) ≤
      Real.exp (-s * a) * μ.expectation (fun ω => Real.exp (s * X ω)) := by
  let : MeasurableSpace Ω := ⊤
  have h := measure_ge_le_exp_mul_mgf (μ := μ.toPMF.toMeasure) (X := X) a hs
    (Integrable.of_finite : Integrable (fun ω => Real.exp (s * X ω)) μ.toPMF.toMeasure)
  simpa only [mgf, finiteLaw_integral, finiteLaw_probability_measure] using h

end Oberwolfach
