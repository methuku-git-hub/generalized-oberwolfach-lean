module

public import Oberwolfach.PartitionCellLaw
public import Oberwolfach.SubsetExchangeCount

@[expose] public section

/-! Exact means and concentration for a specified cell. The test set is
fixed in the full label domain; it may be a neighbourhood of an external root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedPartition_cell_size_le {V : Type*} [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)] (a : Fin k) :
    d a ≤ Fintype.card V := by
  let P := Classical.choice (inferInstance : Nonempty (FixedPartition V k d))
  rw [← (fixedPartitionCell P a).2]
  exact Finset.card_le_univ _

theorem fixedPartition_cell_mean {V : Type*} [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (a : Fin k) (A : Finset V) :
    (FiniteLaw.uniform (FixedPartition V k d)).expectation
      (fun P => ((A ∩ (fixedPartitionCell P a).1).card : ℝ)) =
      (A.card : ℝ) * ((d a : ℝ) / Fintype.card V) := by
  have hr := fixedPartition_cell_size_le (V := V) (d := d) a
  letI := fixedSubset_nonempty hr
  have h := fixedSubset_intersection_mean hr A
  rw [← fixedPartition_cell_uniform a, finiteLaw_map_expectation] at h
  exact h

theorem fixedPartition_cell_count_tail {V : Type*} [Fintype V]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (a : Fin k) (A : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.uniform (FixedPartition V k d)).probability
      (fun P => t ≤ |((A ∩ (fixedPartitionCell P a).1).card : ℝ) -
        (A.card : ℝ) * ((d a : ℝ) / Fintype.card V)|) ≤
      2 * Real.exp (-2 * t ^ 2 / (d a : ℝ)) := by
  have hr := fixedPartition_cell_size_le (V := V) (d := d) a
  letI := fixedSubset_nonempty hr
  let f (S : FixedSubset V (d a)) := ((A ∩ S.1).card : ℝ)
  have hm (s : ℝ) : (FiniteLaw.uniform (FixedSubset V (d a))).expectation
      (fun S => Real.exp (s * (f S - (FiniteLaw.uniform (FixedSubset V (d a))).expectation f))) ≤
      Real.exp (s ^ 2 * (d a : ℝ) / 8) := by
    simpa only [one_pow, mul_one] using fixedSubset_mgf hr f (show (0 : ℝ) ≤ 1 by norm_num)
      (fun S u v => swap_subset_intersection_change A S.1 u v) s
  have hh := finiteLaw_mgf_absolute_tail (FiniteLaw.uniform (FixedSubset V (d a))) f
    (show (0 : ℝ) ≤ d a by positivity) hm ht
  change (FiniteLaw.uniform (FixedSubset V (d a))).probability
    (fun S => t ≤ |((A ∩ S.1).card : ℝ) -
      (FiniteLaw.uniform (FixedSubset V (d a))).expectation f|) ≤ _ at hh
  rw [fixedSubset_intersection_mean hr A] at hh
  rw [← fixedPartition_cell_uniform a, finiteLaw_map_probability] at hh
  exact hh

end Oberwolfach
