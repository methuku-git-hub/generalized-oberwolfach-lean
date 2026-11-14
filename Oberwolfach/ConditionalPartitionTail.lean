module

public import Oberwolfach.ConditionedCellCounts
public import Oberwolfach.ConditionedMeanShift

@[expose] public section

/-! Conditional cell counts measured against the original full-domain
mean. The deterministic loss is twice the number of prescribed vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedCellTest_full_mean_shift {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (A : Finset X) (B : Finset Y) (a : Fin k) :
    |(rootTestCount r A a : ℝ) + (B.card : ℝ) * ((d a : ℝ) / Fintype.card Y) -
      ((A.card : ℝ) + B.card) *
        (((rootCellSize r a : ℝ) + d a) / ((Fintype.card X : ℝ) + Fintype.card Y))| ≤
      2 * Fintype.card X := by
  have hr : rootCellSize r a ≤ Fintype.card X := Fintype.card_subtype_le _
  have he := fixedPartition_cell_size_le (V := Y) (d := d) a
  have hu : rootTestCount r A a ≤ Fintype.card X :=
    (Finset.card_filter_le A _).trans (Finset.card_le_univ _)
  apply conditioned_cell_mean_shift (Nat.cast_nonneg _) (by exact_mod_cast Fintype.card_pos)
    ⟨Nat.cast_nonneg _, by exact_mod_cast hr⟩
    ⟨Nat.cast_nonneg _, by exact_mod_cast he⟩
    ⟨Nat.cast_nonneg _, by exact_mod_cast hu⟩
    ⟨Nat.cast_nonneg _, by exact_mod_cast Finset.card_le_univ A⟩
    ⟨Nat.cast_nonneg _, by exact_mod_cast Finset.card_le_univ B⟩

theorem rootedCellTest_full_mean_tail {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (A : Finset X) (B : Finset Y) (a : Fin k) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
      (fun P => t + 2 * Fintype.card X ≤ |(rootedCellTest P A B a : ℝ) -
        ((A.card : ℝ) + B.card) *
          (((rootCellSize r a : ℝ) + d a) / ((Fintype.card X : ℝ) + Fintype.card Y))|) ≤
      2 * Real.exp (-2 * t ^ 2 / (d a : ℝ)) := by
  apply le_trans (finiteLaw_probability_mono _ _ _ ?_) (rootedCellTest_tail r d A B a ht)
  intro P hP
  have hshift := rootedCellTest_full_mean_shift r d A B a
  have htriangle := abs_sub_le (rootedCellTest P A B a : ℝ)
    (rootTestCount r A a + (B.card : ℝ) * ((d a : ℝ) / Fintype.card Y))
    (((A.card : ℝ) + B.card) *
      (((rootCellSize r a : ℝ) + d a) / ((Fintype.card X : ℝ) + Fintype.card Y)))
  linarith

end Oberwolfach
