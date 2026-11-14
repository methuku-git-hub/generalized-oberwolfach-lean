module

public import Oberwolfach.ConditionalPartitionTail

@[expose] public section

/-! A fixed neighbourhood whose original degree is near D gives a
conditional interface-degree estimate, with all root and mean errors
measured on the original vertex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem scaled_degree_mean_error {N m q D ε : ℝ}
    (hN : 0 < N) (hm : 0 ≤ m) (hdegree : |q - D| ≤ ε * N) :
    |q * (m / N) - D * (m / N)| ≤ ε * m := by
  rw [← sub_mul, abs_mul, abs_of_nonneg (div_nonneg hm hN.le)]
  calc
    |q - D| * (m / N) ≤ (ε * N) * (m / N) :=
      mul_le_mul_of_nonneg_right hdegree (div_nonneg hm hN.le)
    _ = ε * m := by field_simp

theorem rootedPartition_degree_tail {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (A : Finset X) (B : Finset Y) (a : Fin k) (D ε η t : ℝ)
    (ht : 0 ≤ t)
    (hdegree : |((A.card : ℝ) + B.card) - D| ≤
      ε * ((Fintype.card X : ℝ) + Fintype.card Y))
    (hmargin : t + 2 * Fintype.card X + ε * (rootCellSize r a + d a) ≤
      η * (rootCellSize r a + d a)) :
    (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
      (fun P => η * (rootCellSize r a + d a) ≤
        |(rootedCellTest P A B a : ℝ) -
          D * (((rootCellSize r a : ℝ) + d a) /
            ((Fintype.card X : ℝ) + Fintype.card Y))|) ≤
      2 * Real.exp (-2 * t ^ 2 / (d a : ℝ)) := by
  have hn : (0 : ℝ) < (Fintype.card X : ℝ) + Fintype.card Y := by
    have hy : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
    positivity
  have hmean := scaled_degree_mean_error hn
    (show (0 : ℝ) ≤ (rootCellSize r a : ℝ) + d a by positivity) hdegree
  apply le_trans (finiteLaw_probability_mono _ _ _ ?_)
    (rootedCellTest_full_mean_tail r d A B a ht)
  intro P hP
  have htriangle := abs_sub_le (rootedCellTest P A B a : ℝ)
    ((((A.card : ℝ) + B.card)) *
      (((rootCellSize r a : ℝ) + d a) / ((Fintype.card X : ℝ) + Fintype.card Y)))
    (D * (((rootCellSize r a : ℝ) + d a) / ((Fintype.card X : ℝ) + Fintype.card Y)))
  linarith

end Oberwolfach
