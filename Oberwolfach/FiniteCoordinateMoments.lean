module

public import Oberwolfach.FiniteCoordinateIndependence
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-! Products of functions of two distinct coordinates in the original
finite product law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_two_coordinate_product {I : Type*} [Fintype I] [DecidableEq I]
    {State : I → Type*} [∀ i,Fintype (State i)]
    (μ : ∀ i,FiniteLaw (State i)) (i j : I) (hij : i≠j)
    (X : State i → ℝ) (Y : State j → ℝ) :
    (FiniteLaw.pi μ).expectation (fun σ => X (σ i)*Y (σ j))=
      (μ i).expectation X*(μ j).expectation Y := by
  let : ∀ e,MeasurableSpace (State e) := fun _ => ⊤
  let : ∀ e,MeasurableSingletonClass (State e) := fun _ => ⟨fun _ => trivial⟩
  have hcoord : iIndepFun (fun (e : I) (σ : ∀ k,State k) => σ e)
      (FiniteLaw.pi μ).toPMF.toMeasure := by
    rw [finiteLaw_pi_measure]
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hXY := (hcoord.indepFun hij).comp (measurable_of_finite X) (measurable_of_finite Y)
  have hh := hXY.integral_mul_eq_mul_integral
    (measurable_of_finite (fun σ : ∀ k,State k => X (σ i))).aestronglyMeasurable
    (measurable_of_finite (fun σ : ∀ k,State k => Y (σ j))).aestronglyMeasurable
  change (∫ σ,X (σ i)*Y (σ j) ∂(FiniteLaw.pi μ).toPMF.toMeasure)=
    (∫ σ,X (σ i) ∂(FiniteLaw.pi μ).toPMF.toMeasure)*
    (∫ σ,Y (σ j) ∂(FiniteLaw.pi μ).toPMF.toMeasure) at hh
  simpa only [finiteLaw_integral,finiteLaw_coordinate_expectation] using hh

theorem finiteLaw_expectation_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : FiniteLaw Ω) (X : I → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i,X i ω)=∑ i,μ.expectation (X i) := by
  simp only [FiniteLaw.expectation,Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteLaw_expectation_add {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.expectation (fun ω => X ω+Y ω)=μ.expectation X+μ.expectation Y := by
  simp only [FiniteLaw.expectation,mul_add,Finset.sum_add_distrib]

end Oberwolfach
