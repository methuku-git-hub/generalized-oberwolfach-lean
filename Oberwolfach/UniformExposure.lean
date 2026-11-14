module

public import Oberwolfach.FiniteUniform

@[expose] public section

/-! A conditional exposure step. The continuation law is allowed to
depend on the exposed value; no independence is imposed on that law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_mgf_bound
    {Ω : Type*} [Fintype Ω] {Γ : Ω → Type*} [∀ ω, Fintype (Γ ω)]
    (μ : FiniteLaw Ω) (ν : ∀ ω, FiniteLaw (Γ ω)) (X : (Σ ω, Γ ω) → ℝ)
    {c v : ℝ} (hc : 0 ≤ c)
    (hdiam : ∀ x y, |(ν x).expectation (fun z => X ⟨x,z⟩) -
      (ν y).expectation (fun z => X ⟨y,z⟩)| ≤ c)
    (htail : ∀ x u, (ν x).expectation (fun z =>
      Real.exp (u * (X ⟨x,z⟩ - (ν x).expectation (fun w => X ⟨x,w⟩)))) ≤
        Real.exp (u ^ 2 * v / 8)) (u : ℝ) :
    (μ.sigma ν).expectation (fun z => Real.exp (u * (X z - (μ.sigma ν).expectation X))) ≤
      Real.exp (u ^ 2 * (v + c ^ 2) / 8) := by
  let g (x : Ω) := (ν x).expectation (fun z => X ⟨x,z⟩)
  have hmean : (μ.sigma ν).expectation X = μ.expectation g := finiteLaw_sigma_expectation μ ν X
  have hfactor (x : Ω) :
      (ν x).expectation (fun z => Real.exp (u * (X ⟨x,z⟩ - (μ.sigma ν).expectation X))) =
      Real.exp (u * (g x - μ.expectation g)) *
        (ν x).expectation (fun z => Real.exp (u * (X ⟨x,z⟩ - g x))) := by
    rw [← finiteLaw_expectation_const_mul]
    apply congrArg (ν x).expectation
    funext z
    rw [← Real.exp_add, hmean]
    congr 1
    ring
  rw [finiteLaw_sigma_expectation]
  simp_rw [hfactor]
  calc
    _ ≤ μ.expectation (fun x => Real.exp (u ^ 2 * v / 8) *
        Real.exp (u * (g x - μ.expectation g))) := by
      apply finiteLaw_expectation_mono
      intro x
      have hh := mul_le_mul_of_nonneg_left (htail x u)
        (Real.exp_pos (u * (g x - μ.expectation g))).le
      simpa only [g, mul_comm] using hh
    _ = Real.exp (u ^ 2 * v / 8) * μ.expectation
        (fun x => Real.exp (u * (g x - μ.expectation g))) :=
      finiteLaw_expectation_const_mul μ _ _
    _ ≤ Real.exp (u ^ 2 * v / 8) * Real.exp (u ^ 2 * c ^ 2 / 8) := by
      apply mul_le_mul_of_nonneg_left (finiteLaw_mgf_of_diameter μ g hc hdiam u)
      positivity
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem finiteLaw_mgf_absolute_tail
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {v : ℝ} (hv : 0 ≤ v)
    (hmgf : ∀ u, μ.expectation (fun ω => Real.exp (u * (X ω - μ.expectation X))) ≤
      Real.exp (u ^ 2 * v / 8)) {t : ℝ} (ht : 0 ≤ t) :
    μ.probability (fun ω => t ≤ |X ω - μ.expectation X|) ≤
      2 * Real.exp (-2 * t ^ 2 / v) := by
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
  have hh := subgaussian_absolute_tail hsub ht
  rw [finiteLaw_probability_measure] at hh
  have he : -t ^ 2 / (2 * (q : ℝ)) = -2 * t ^ 2 / v := by rw [hq]; ring
  simpa only [he] using hh

end Oberwolfach
