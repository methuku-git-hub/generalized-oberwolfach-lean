module

public import Oberwolfach.ChernoffFromMGF

@[expose] public section

/-! Chernoff bounds for independent finite random variables in [0,1]. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finiteLaw_pi_expectation_sum
    {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (X : ∀ i, Ω i → ℝ) :
    (FiniteLaw.pi μ).expectation (fun σ => ∑ i, X i (σ i)) =
      ∑ i, (μ i).expectation (X i) := by
  let : ∀ i, MeasurableSpace (Ω i) := fun _ => ⊤
  have he : ∀ i, (FiniteLaw.pi μ).expectation (fun σ => X i (σ i)) =
      (μ i).expectation (X i) := fun i => finiteLaw_coordinate_expectation μ i (X i)
  simp only [FiniteLaw.expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => he i)

theorem finiteLaw_nonnegative_zero_mean
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hzero : μ.expectation X = 0)
    (ω : Ω) (hω : 0 < μ.mass ω) : X ω = 0 := by
  have hh : μ.mass ω * X ω ≤ 0 := by
    rw [← hzero]
    exact Finset.single_le_sum (fun x _ => mul_nonneg (μ.nonneg x) (hX x)) (Finset.mem_univ ω)
  exact le_antisymm (nonpos_of_mul_nonpos_right hh hω) (hX ω)

theorem finiteLaw_independent_chernoff
    {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (he : 0 ≤ ε) (he1 : ε ≤ 1) :
    let a := (FiniteLaw.pi μ).expectation (fun σ => ∑ i, X i (σ i))
    (FiniteLaw.pi μ).probability (fun σ => ε * a ≤ |(∑ i, X i (σ i)) - a|) ≤
      2 * Real.exp (-ε ^ 2 * a / 3) := by
  dsimp only
  rw [finiteLaw_pi_expectation_sum]
  apply finiteLaw_poisson_mgf_absolute_tail _ _ _
    (finiteLaw_independent_unit_interval_mgf μ X hX) he he1
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun ω _ => mul_nonneg ((μ i).nonneg ω) (hX i ω).1))

theorem finiteLaw_independent_chernoff_large
    {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Ω i)) (X : ∀ i, Ω i → ℝ)
    (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (ha : 0 < (FiniteLaw.pi μ).expectation (fun σ => ∑ i, X i (σ i)))
    {t : ℝ} (ht : (FiniteLaw.pi μ).expectation (fun σ => ∑ i, X i (σ i)) ≤ t) :
    (FiniteLaw.pi μ).probability (fun σ => t ≤ ∑ i, X i (σ i)) ≤
      (Real.exp 1 * (FiniteLaw.pi μ).expectation (fun σ => ∑ i, X i (σ i)) / t) ^ t := by
  rw [finiteLaw_pi_expectation_sum] at ha ht ⊢
  exact finiteLaw_poisson_mgf_large_tail _ _ ha
    (finiteLaw_independent_unit_interval_mgf μ X hX) ht

end Oberwolfach
