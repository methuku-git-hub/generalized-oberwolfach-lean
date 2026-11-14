module

public import Oberwolfach.SubsetCounts

@[expose] public section

/-! A finite expansion of the intersection-count probability generating function. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem intersection_power_expansion {V : Type*} (A S : Finset V) (q : ℝ) :
    q ^ (A ∩ S).card = ∑ T ∈ A.powerset,
      (q - 1) ^ T.card * (if T ⊆ S then 1 else 0) := by
  have hp : (∏ x ∈ A, (1 + (q - 1) * (if x ∈ S then (1 : ℝ) else 0))) =
      q ^ (A ∩ S).card := by
    have he (x : V) : 1 + (q - 1) * (if x ∈ S then (1 : ℝ) else 0) =
        if x ∈ S then q else 1 := by split_ifs <;> ring
    simp_rw [he]
    simp
  rw [← hp, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_boole]
  rfl

theorem finiteLaw_intersection_power_expectation
    {V : Type*} [Fintype V] {r : ℕ} (μ : FiniteLaw (FixedSubset V r))
    (A : Finset V) (q : ℝ) :
    μ.expectation (fun S => q ^ (A ∩ S.1).card) =
      ∑ T ∈ A.powerset, (q - 1) ^ T.card * μ.probability (fun S => T ⊆ S.1) := by
  simp only [FiniteLaw.expectation, intersection_power_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  unfold FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h : T ⊆ S.1 <;> simp [h, mul_comm]

end Oberwolfach
