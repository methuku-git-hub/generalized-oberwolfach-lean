module

public import Oberwolfach.RootedPartitions
public import Oberwolfach.PartitionCellCounts
public import Oberwolfach.UniformConditioning

@[expose] public section

/-! Conditional intersection estimates after fixing vertex classes. The
root contribution is deterministic; the remaining cell has the exact
uniform partition law proved in RootedPartitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rootTestCount {X : Type*} [Fintype X] {k : ℕ}
    (r : X → Fin k) (A : Finset X) (a : Fin k) : ℕ :=
  (A.filter (fun x => r x = a)).card

def rootedCellTest {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} {r : X → Fin k} {d : Fin k → ℕ}
    (P : RootedPartition X Y k r d) (A : Finset X) (B : Finset Y) (a : Fin k) : ℕ :=
  ((A.disjSum B).filter (fun v => P.1.1 v = a)).card

theorem rootedCellTest_eq {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} {r : X → Fin k} {d : Fin k → ℕ}
    (P : RootedPartition X Y k r d) (A : Finset X) (B : Finset Y) (a : Fin k) :
    rootedCellTest P A B a = rootTestCount r A a +
      (B ∩ (fixedPartitionCell (rootPartitionRestrict P) a).1).card := by
  unfold rootedCellTest rootTestCount
  rw [Finset.card_filter, Finset.sum_disjSum]
  simp only [P.2]
  rw [← Finset.card_filter, ← Finset.card_filter]
  congr 1
  congr 1
  ext y
  simp [fixedPartitionCell, rootPartitionRestrict]

theorem rootedCellTest_mean {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (A : Finset X) (B : Finset Y) (a : Fin k) :
    (FiniteLaw.uniform (RootedPartition X Y k r d)).expectation
      (fun P => (rootedCellTest P A B a : ℝ)) =
      rootTestCount r A a + (B.card : ℝ) * ((d a : ℝ) / Fintype.card Y) := by
  simp only [rootedCellTest_eq, Nat.cast_add, FiniteLaw.expectation, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, FiniteLaw.total, one_mul]
  have h := fixedPartition_cell_mean (d := d) a B
  rw [← rootedPartition_uniform_restriction r d, finiteLaw_map_expectation] at h
  exact congrArg (fun t : ℝ => rootTestCount r A a + t) h

theorem rootedCellTest_tail {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (A : Finset X) (B : Finset Y) (a : Fin k) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
      (fun P => t ≤ |(rootedCellTest P A B a : ℝ) -
        (rootTestCount r A a + (B.card : ℝ) * ((d a : ℝ) / Fintype.card Y))|) ≤
      2 * Real.exp (-2 * t ^ 2 / (d a : ℝ)) := by
  have h := fixedPartition_cell_count_tail (d := d) a B ht
  rw [← rootedPartition_uniform_restriction r d, finiteLaw_map_probability] at h
  simpa only [rootedCellTest_eq, Nat.cast_add, add_sub_add_left_eq_sub] using h

end Oberwolfach
