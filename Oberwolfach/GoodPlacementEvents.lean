module

public import Oberwolfach.PartitionPlacementBounds
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Intersecting a specified placement event with one common good event.
This derives the required conditional survival estimate without changing
the partition law or asserting independence of the two events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_good_intersection {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E Good : Ω → Prop) (δ : ℝ)
    (hgood : 1 - δ ≤ μ.probability Good) :
    μ.probability E - δ ≤ μ.probability (fun ω => E ω ∧ Good ω) := by
  have hcomp := finiteLaw_probability_compl μ Good
  have h : μ.probability E ≤ μ.probability (fun ω => E ω ∧ Good ω) +
      μ.probability (fun ω => ¬ Good ω) := by
    unfold FiniteLaw.probability
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    by_cases he : E ω <;> by_cases hg : Good ω <;> simp [he, hg, μ.nonneg]
  linarith

theorem finiteLaw_good_intersection_relative {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E Good : Ω → Prop) (δ ε : ℝ)
    (hgood : 1 - δ ≤ μ.probability Good)
    (hscale : δ ≤ ε * μ.probability E) :
    (1 - ε) * μ.probability E ≤ μ.probability (fun ω => E ω ∧ Good ω) := by
  have h := finiteLaw_good_intersection μ E Good δ hgood
  nlinarith

theorem fixedPartition_good_joint_placement {I V : Type*} [Fintype I] [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (x : I ↪ V) (a : I ↪ Fin k) (m : ℕ) (hm : ∀ i, d (a i) = m)
    (hn : 0 < Fintype.card V)
    (Good : FixedPartition V k d → Prop) (δ ε : ℝ) (hε : 0 ≤ ε)
    (hgood : 1 - δ ≤ (FiniteLaw.uniform (FixedPartition V k d)).probability Good)
    (hscale : δ ≤ ε * ((m : ℝ) / Fintype.card V) ^ Fintype.card I) :
    (1 - ε) * (FiniteLaw.uniform (FixedPartition V k d)).probability
        (fun P => ∀ i, P.1 (x i) = a i) ≤
      (FiniteLaw.uniform (FixedPartition V k d)).probability
        (fun P => (∀ i, P.1 (x i) = a i) ∧ Good P) := by
  apply finiteLaw_good_intersection_relative _ _ _ δ ε hgood
  exact hscale.trans (mul_le_mul_of_nonneg_left
    (fixedPartition_joint_placement_lower x a m hm hn) hε)

end Oberwolfach
