module

public import Oberwolfach.FiniteSampling
public import Oberwolfach.Concentration
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-!
Identification of the explicit finite categorical law with mathlib's
probability measures. This supplies the independence required by the
concentration theorem, rather than assuming independence for the finite
product constructed in `FiniteSampling`.
-/
set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Oberwolfach

namespace FiniteLaw
def toPMF {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (μ.mass ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => μ.nonneg ω), μ.total]
    simp)
end FiniteLaw

theorem finiteLaw_integral
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    ∫ ω, X ω ∂μ.toPMF.toMeasure = μ.expectation X := by
  rw [PMF.integral_eq_sum]
  simp only [FiniteLaw.toPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (μ.nonneg _), smul_eq_mul, FiniteLaw.expectation]

theorem finiteLaw_probability_measure
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : FiniteLaw Ω) (A : Ω → Prop) :
    μ.toPMF.toMeasure.real {ω | A ω} = μ.probability A := by
  classical
  have hnonneg (ω : Ω) : 0 ≤ (if A ω then μ.mass ω else 0) := by
    split_ifs <;> (first | exact μ.nonneg ω | exact le_refl _)
  have heq : μ.toPMF.toMeasure {ω | A ω} = ENNReal.ofReal (μ.probability A) := by
    rw [PMF.toMeasure_apply_fintype, FiniteLaw.probability,
      ENNReal.ofReal_sum_of_nonneg (fun ω _ => hnonneg ω)]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases ha : A ω <;> simp [Set.indicator, FiniteLaw.toPMF, ha]
  rw [measureReal_def, heq, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg (fun ω _ => hnonneg ω)

theorem finiteLaw_pi_measure
    {I : Type*} [Fintype I] [DecidableEq I]
    {State : I → Type*} [∀ i, Fintype (State i)]
    [∀ i, MeasurableSpace (State i)] [∀ i, MeasurableSingletonClass (State i)]
    (μ : ∀ i, FiniteLaw (State i)) :
    (FiniteLaw.pi μ).toPMF.toMeasure = Measure.pi (fun i => (μ i).toPMF.toMeasure) := by
  apply Measure.ext_of_singleton
  intro σ
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change ENNReal.ofReal (∏ i, (μ i).mass (σ i)) =
    ∏ i, ENNReal.ofReal ((μ i).mass (σ i))
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => (μ i).nonneg (σ i))

theorem finiteLaw_coordinate_expectation
    {I : Type*} [Fintype I] [DecidableEq I]
    {State : I → Type*} [∀ i, Fintype (State i)]
    [∀ i, MeasurableSpace (State i)] [∀ i, MeasurableSingletonClass (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (i : I) (X : State i → ℝ) :
    (FiniteLaw.pi μ).expectation (fun σ => X (σ i)) = (μ i).expectation X := by
  rw [← finiteLaw_integral, finiteLaw_pi_measure, ← finiteLaw_integral]
  have hm := measurePreserving_eval (fun j => (μ j).toPMF.toMeasure) i
  rw [← hm.map_eq]
  exact (integral_map_of_stronglyMeasurable hm.measurable
    (measurable_of_finite X).stronglyMeasurable).symm

/-- The coordinate variables of the explicitly constructed categorical
law are independent. Arbitrary functions of one coordinate retain this
independence. -/
theorem finiteLaw_coordinate_independence
    {I : Type*} [Fintype I] [DecidableEq I]
    {State : I → Type*} [∀ i, Fintype (State i)]
    [∀ i, MeasurableSpace (State i)] [∀ i, MeasurableSingletonClass (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (X : ∀ i, State i → ℝ) :
    iIndepFun (fun i σ => X i (σ i)) (FiniteLaw.pi μ).toPMF.toMeasure := by
  rw [finiteLaw_pi_measure]
  exact iIndepFun_pi (fun i => (measurable_of_finite (X i)).aemeasurable)

/-- Hoeffding's inequality for the exact finite product law. Each summand
depends on one original coordinate; the displayed centre is its finite
expectation under that same law. -/
theorem finiteLaw_bounded_coordinate_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    {State : I → Type*} [∀ i, Fintype (State i)]
    [∀ i, MeasurableSpace (State i)] [∀ i, MeasurableSingletonClass (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (X : ∀ i, State i → ℝ)
    (a b : I → ℝ) (s : Finset I)
    (hbounded : ∀ i ∈ s, ∀ x, X i x ∈ Set.Icc (a i) (b i))
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi μ).probability
      (fun σ => t ≤ |(∑ i ∈ s, X i (σ i)) -
        ∑ i ∈ s, (μ i).expectation (X i)|) ≤
      2 * Real.exp (-2 * t ^ 2 / (∑ i ∈ s, (b i - a i) ^ 2)) := by
  have hind := finiteLaw_coordinate_independence μ X
  have htail := boundedIndependentSum_tail (μ := (FiniteLaw.pi μ).toPMF.toMeasure)
    (fun i (σ : ∀ j, State j) => X i (σ i)) a b s hind
    (fun i _ => (measurable_of_finite (fun (σ : ∀ j, State j) => X i (σ i))).aemeasurable)
    (fun i hi => Filter.Eventually.of_forall (fun σ => hbounded i hi (σ i))) ht
  simp only [finiteLaw_integral, finiteLaw_probability_measure,
    finiteLaw_coordinate_expectation] at htail
  exact htail

/-- The raw directed-colour cut estimate is a concentration statement over
physical edges. `forward e` and `reverse e` may both hold; the probability
law still has exactly one colour and one direction for edge `e`. -/
theorem categoricalDirection_cut_tail
    {E : Type*} [Fintype E] [DecidableEq E] {k : ℕ}
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    (a : Fin k) (forward reverse : E → Prop)
    [DecidablePred forward] [DecidablePred reverse]
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.pi (fun _ : E => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
      (fun σ => t ≤ |(∑ e, directedCutContribution a (forward e) (reverse e) (σ e)) -
        ρ a / 2 * (∑ e : E, ((if forward e then (1 : ℝ) else 0) +
          (if reverse e then (1 : ℝ) else 0)))|) ≤
      2 * Real.exp (-2 * t ^ 2 / Fintype.card E) := by
  classical
  have hh := finiteLaw_bounded_coordinate_sum
    (fun _ : E => FiniteLaw.categoricalDirection ρ hρ htotal)
    (fun e => directedCutContribution a (forward e) (reverse e))
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) Finset.univ
    (fun e _ s => directedCutContribution_bounds a (forward e) (reverse e) s) ht
  simpa only [categoricalDirection_expected_cut, ← Finset.mul_sum, sub_zero, one_pow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hh

end Oberwolfach
