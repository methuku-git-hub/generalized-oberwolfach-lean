module

public import Oberwolfach.UniformExposure

@[expose] public section

/-! Both one-sided estimates with the same variance as the exposure bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Oberwolfach

theorem finiteLaw_mgf_one_sided_tails
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {v : ℝ} (hv : 0 ≤ v)
    (hmgf : ∀ u, μ.expectation (fun ω => Real.exp (u * (X ω - μ.expectation X))) ≤
      Real.exp (u ^ 2 * v / 8)) {t : ℝ} (ht : 0 ≤ t) :
    μ.probability (fun ω => t ≤ X ω - μ.expectation X) ≤ Real.exp (-2 * t ^ 2 / v) ∧
    μ.probability (fun ω => t ≤ μ.expectation X - X ω) ≤ Real.exp (-2 * t ^ 2 / v) := by
  let : MeasurableSpace Ω := ⊤
  let q : ℝ≥0 := ⟨v / 4, by positivity⟩
  have hq : (q : ℝ) = v / 4 := rfl
  have hsub : HasSubgaussianMGF (fun ω => X ω - μ.expectation X) q μ.toPMF.toMeasure := by
    refine ⟨fun _ => Integrable.of_finite, ?_⟩
    intro u
    simp only [mgf, finiteLaw_integral]
    convert hmgf u using 1
    rw [hq]
    congr 1
    ring
  have he : -t ^ 2 / (2 * (q : ℝ)) = -2 * t ^ 2 / v := by rw [hq]; ring
  constructor
  · have hh := hsub.measure_ge_le ht
    rwa [finiteLaw_probability_measure, he] at hh
  · have hh := hsub.neg.measure_ge_le ht
    simpa only [Pi.neg_apply, neg_sub, finiteLaw_probability_measure, he] using hh

end Oberwolfach
