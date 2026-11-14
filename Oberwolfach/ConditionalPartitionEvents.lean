module

public import Oberwolfach.ConditionalPartitionTail

@[expose] public section

/-! One conditional common event for a fixed family of cell-count tests.
No test domain is chosen after the partition is sampled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedPartition_common_counts {X Y J : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (tests : Finset J) (A : J → Finset X) (B : J → Finset Y) (a : J → Fin k)
    (t : J → ℝ) (ht : ∀ j ∈ tests, 0 ≤ t j) :
    1 - ∑ j ∈ tests, 2 * Real.exp (-2 * (t j) ^ 2 / (d (a j) : ℝ)) ≤
      (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
        (fun P => ∀ j ∈ tests,
          |(rootedCellTest P (A j) (B j) (a j) : ℝ) -
            (((A j).card : ℝ) + (B j).card) *
              (((rootCellSize r (a j) : ℝ) + d (a j)) /
                ((Fintype.card X : ℝ) + Fintype.card Y))| < t j + 2 * Fintype.card X) := by
  have h := finiteLaw_common_event_lower (FiniteLaw.uniform (RootedPartition X Y k r d)) tests
    (fun j P => t j + 2 * Fintype.card X ≤
      |(rootedCellTest P (A j) (B j) (a j) : ℝ) -
        (((A j).card : ℝ) + (B j).card) *
          (((rootCellSize r (a j) : ℝ) + d (a j)) /
            ((Fintype.card X : ℝ) + Fintype.card Y))|)
    (fun j => 2 * Real.exp (-2 * (t j) ^ 2 / (d (a j) : ℝ)))
    (fun j hj => rootedCellTest_full_mean_tail r d (A j) (B j) (a j) (ht j hj))
  simpa only [not_le] using h

set_option maxHeartbeats 1000000 in
theorem uniform_root_condition_common_event {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (FixedPartition (X ⊕ Y) k (fun a => rootCellSize r a + d a))]
    [Nonempty (RootedPartition X Y k r d)]
    (Good : FixedPartition (X ⊕ Y) k (fun a => rootCellSize r a + d a) → Prop)
    (ε : ℝ)
    (h : 1 - ε ≤ (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
      (fun P => Good P.1)) :
    (FiniteLaw.uniform (FixedPartition (X ⊕ Y) k (fun a => rootCellSize r a + d a))).probability
      (fun P => ∀ x, P.1 (Sum.inl x) = r x) * (1 - ε) ≤
    (FiniteLaw.uniform (FixedPartition (X ⊕ Y) k (fun a => rootCellSize r a + d a))).probability
      (fun P => (∀ x, P.1 (Sum.inl x) = r x) ∧ Good P) := by
  rw [uniform_probability_intersection]
  exact mul_le_mul_of_nonneg_left h (finiteLaw_probability_nonneg _ _)

end Oberwolfach
