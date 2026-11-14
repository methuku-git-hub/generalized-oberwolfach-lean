module

public import Oberwolfach.SubsetExchangeCount

@[expose] public section

/-! Normalized intersection estimates for fixed tests, including external graph roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_normalized_count_mean {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (hrpos : 0 < r) (A : Finset V) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => ((A ∩ S.1).card : ℝ) / r) = (A.card : ℝ) / Fintype.card V := by
  have hrreal : (r : ℝ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have he : (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => ((A ∩ S.1).card : ℝ) / r) =
      (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => ((A ∩ S.1).card : ℝ)) / r := by
    simp only [FiniteLaw.expectation, div_eq_mul_inv, ← mul_assoc, Finset.sum_mul]
  rw [he, fixedSubset_intersection_mean hr]
  field_simp

theorem fixedSubset_normalized_count_tail {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r ≤ Fintype.card V) (hrpos : 0 < r) (A : Finset V)
    {t : ℝ} (ht : 0 ≤ t) :
    (FiniteLaw.uniform (FixedSubset V r)).probability
      (fun S => t ≤ |((A ∩ S.1).card : ℝ) / r - (A.card : ℝ) / Fintype.card V|) ≤
      2 * Real.exp (-2 * (r : ℝ) * t ^ 2) := by
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hrpos
  let f (S : FixedSubset V r) := ((A ∩ S.1).card : ℝ) / r
  have hex : ∀ S u v, |f S - f (fixedSubsetMap (Equiv.swap u v) S)| ≤ 1 / r := by
    intro S u v
    dsimp only [f, fixedSubsetMap]
    rw [← sub_div, abs_div, abs_of_pos hrreal]
    exact (div_le_div_iff_of_pos_right hrreal).mpr (swap_subset_intersection_change A S.1 u v)
  have hm (s : ℝ) : (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => Real.exp (s * (f S - (FiniteLaw.uniform (FixedSubset V r)).expectation f))) ≤
      Real.exp (s ^ 2 * (1 / (r : ℝ)) / 8) := by
    convert fixedSubset_mgf hr f (show 0 ≤ 1 / (r : ℝ) by positivity) hex s using 1
    congr 1
    field_simp
  have hh := finiteLaw_mgf_absolute_tail (FiniteLaw.uniform (FixedSubset V r)) f
    (show 0 ≤ 1 / (r : ℝ) by positivity) hm ht
  change (FiniteLaw.uniform (FixedSubset V r)).probability
      (fun S => t ≤ |((A ∩ S.1).card : ℝ) / r -
        (FiniteLaw.uniform (FixedSubset V r)).expectation (fun S => ((A ∩ S.1).card : ℝ) / r)|) ≤ _ at hh
  rw [fixedSubset_normalized_count_mean hr hrpos] at hh
  convert hh using 1
  congr 2
  field_simp

theorem fixedSubset_simultaneous_normalized_counts
    {V J : Type*} [Fintype V] {r : ℕ} [Nonempty (FixedSubset V r)]
    (hr : r ≤ Fintype.card V) (hrpos : 0 < r) (tests : Finset J) (A : J → Finset V)
    {t : ℝ} (ht : 0 ≤ t) :
    1 - 2 * tests.card * Real.exp (-2 * (r : ℝ) * t ^ 2) ≤
      (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => ∀ j ∈ tests,
        |((A j ∩ S.1).card : ℝ) / r - ((A j).card : ℝ) / Fintype.card V| < t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.uniform (FixedSubset V r)) tests
    (fun j S => t ≤ |((A j ∩ S.1).card : ℝ) / r - ((A j).card : ℝ) / Fintype.card V|)
    (fun _ => 2 * Real.exp (-2 * (r : ℝ) * t ^ 2))
    (fun j _ => fixedSubset_normalized_count_tail hr hrpos (A j) ht)
  simp only [not_le, Finset.sum_const, nsmul_eq_mul] at hh
  convert hh using 1; ring

theorem fixedSubset_normalized_counts_exists
    {V J : Type*} [Fintype V] {r : ℕ} (hr : r ≤ Fintype.card V)
    (hrpos : 0 < r) (tests : Finset J) (A : J → Finset V)
    {t : ℝ} (ht : 0 ≤ t)
    (hsmall : 2 * tests.card * Real.exp (-2 * (r : ℝ) * t ^ 2) < 1) :
    ∃ S : FixedSubset V r, ∀ j ∈ tests,
      |((A j ∩ S.1).card : ℝ) / r - ((A j).card : ℝ) / Fintype.card V| < t := by
  let : Nonempty (FixedSubset V r) := fixedSubset_nonempty hr
  have hh := finiteLaw_common_event_exists (FiniteLaw.uniform (FixedSubset V r)) tests
    (fun j S => t ≤ |((A j ∩ S.1).card : ℝ) / r - ((A j).card : ℝ) / Fintype.card V|)
    (fun _ => 2 * Real.exp (-2 * (r : ℝ) * t ^ 2))
    (fun j _ => fixedSubset_normalized_count_tail hr hrpos (A j) ht)
    (by simpa only [Finset.sum_const, nsmul_eq_mul, mul_left_comm, mul_assoc] using hsmall)
  obtain ⟨S, _, hS⟩ := hh
  exact ⟨S, fun j hj => lt_of_not_ge (hS j hj)⟩

end Oberwolfach
