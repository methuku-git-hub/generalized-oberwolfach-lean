module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! A fixed root whose retained patterns have a common marginal product. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_pattern_uniform_root_sum
    {I A : Type} [Fintype I] [DecidableEq A]
    (R : I → Finset A) (w : I → ℝ) (root : A) (p : A → ℝ) (k : ℝ)
    (hprod : ∀ i, root ∈ R i → (∏ a ∈ R i \ {root}, p a) = k) :
    (∑ i, (if root ∈ R i then w i else 0) * ∏ a ∈ R i \ {root}, p a) =
      k * ∑ i, if root ∈ R i then w i else 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : root ∈ R i
  · simp only [hi, ite_true, hprod i hi]
    ring
  · simp only [hi, ite_false, zero_mul, mul_zero]
end Oberwolfach
