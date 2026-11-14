module

public import Oberwolfach.UniformExposure

@[expose] public section

/-! A zero exponential-moment variance gives equality on every outcome
of positive mass, not only almost surely. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finiteLaw_exp_centered_le_one_constant
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (h : μ.expectation (fun ω => Real.exp (X ω - μ.expectation X)) ≤ 1)
    (ω : Ω) (hω : 0 < μ.mass ω) : X ω = μ.expectation X := by
  let Z (x : Ω) := X x - μ.expectation X
  have hz : μ.expectation Z = 0 := by
    simp only [FiniteLaw.expectation, Z, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, μ.total, one_mul, sub_self]
  let Y (x : Ω) := Real.exp (Z x) - (Z x + 1)
  have hy (x : Ω) : 0 ≤ Y x := sub_nonneg.mpr (Real.add_one_le_exp _)
  have hsum : μ.expectation Y ≤ 0 := by
    have he : μ.expectation Y = μ.expectation (fun x => Real.exp (Z x)) - (μ.expectation Z + 1) := by
      simp only [FiniteLaw.expectation, Y, mul_sub, mul_add, mul_one,
        Finset.sum_sub_distrib, Finset.sum_add_distrib, μ.total]
    rw [he, hz]
    change μ.expectation (fun x => Real.exp (X x - μ.expectation X)) - (0 + 1) ≤ 0
    linarith
  have hs : μ.mass ω * Y ω ≤ 0 :=
    (Finset.single_le_sum (fun x _ => mul_nonneg (μ.nonneg x) (hy x)) (Finset.mem_univ ω)).trans hsum
  have hY : Y ω ≤ 0 := nonpos_of_mul_nonpos_right hs hω
  have heq : Z ω = 0 := by
    by_contra hn
    have hh := Real.add_one_lt_exp hn
    change Real.exp (Z ω) - (Z ω + 1) ≤ 0 at hY
    linarith
  exact sub_eq_zero.mp heq

theorem finiteLaw_zero_mgf_constant
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hmgf : ∀ u, μ.expectation (fun ω => Real.exp (u * (X ω - μ.expectation X))) ≤
      Real.exp (u ^ 2 * 0 / 8))
    (ω : Ω) (hω : 0 < μ.mass ω) : X ω = μ.expectation X := by
  apply finiteLaw_exp_centered_le_one_constant μ X _ ω hω
  simpa using hmgf 1

end Oberwolfach
