module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic

@[expose] public section

/-!
Concentration for sums of independent bounded real random variables.
Independence is imposed on the original random variables. In particular,
different contributions of one physical edge must be combined into a single
variable before this theorem is applied.
-/
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
namespace Oberwolfach

theorem subgaussian_absolute_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * c)) := by
  have hevent : {ω | t ≤ |X ω|} =
      {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hevent]
  have hupper := hX.measure_ge_le ht
  have hlower := hX.neg.measure_ge_le ht
  have hunion := measureReal_union_le (μ := μ) {ω | t ≤ X ω} {ω | t ≤ -X ω}
  simp only [Pi.neg_apply] at hlower
  exact hunion.trans (by linarith)

/-- Hoeffding's two-sided bound, with the sum of squared interval lengths.
The interval and independence assumptions are explicit; no independence
between derived tests or between different colours is required. -/
theorem boundedIndependentSum_tail
    {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (a b : I → ℝ) (s : Finset I)
    (hindep : iIndepFun X μ)
    (hmeas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hbounded : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) - ∑ i ∈ s, ∫ ω, X i ω ∂μ|} ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ i ∈ s, (b i - a i) ^ 2)) := by
  classical
  let Y i ω := X i ω - ∫ z, X i z ∂μ
  let c (i : I) : ℝ≥0 := (‖b i - a i‖₊ / 2) ^ 2
  have hY : iIndepFun Y μ :=
    hindep.comp (fun i x => x - ∫ z, X i z ∂μ) (fun i => by fun_prop)
  have hsub (i : I) (hi : i ∈ s) : HasSubgaussianMGF (Y i) (c i) μ :=
    hasSubgaussianMGF_of_mem_Icc (hmeas i hi) (hbounded i hi)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hY hsub
  have htail := subgaussian_absolute_tail hsum ht
  have hc : ((∑ i ∈ s, c i : ℝ≥0) : ℝ) =
      (∑ i ∈ s, (b i - a i) ^ 2) / 4 := by
    simp only [NNReal.coe_sum, c, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, sq_abs]
    norm_num
  have heq : -t ^ 2 / (2 * ((∑ i ∈ s, c i : ℝ≥0) : ℝ)) =
      -2 * t ^ 2 / (∑ i ∈ s, (b i - a i) ^ 2) := by
    rw [hc]
    ring
  simpa only [Y, Finset.sum_sub_distrib, heq] using htail

end Oberwolfach
