module

public import Oberwolfach.SubsetInclusion
public import Oberwolfach.SubsetGeneratingFunction

@[expose] public section

/-! The exact fixed-size subset law satisfies the binomial generating-function bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_power_bound_ge_one
    {V : Type*} [Fintype V] {r : ℕ} [Nonempty (FixedSubset V r)]
    (hr : r ≤ Fintype.card V) (A : Finset V) {q : ℝ} (hq : 1 ≤ q) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation (fun S => q ^ (A ∩ S.1).card) ≤
      (1 + ((r : ℝ) / Fintype.card V) * (q - 1)) ^ A.card := by
  rw [finiteLaw_intersection_power_expectation]
  calc
    _ ≤ ∑ T ∈ A.powerset, (q - 1) ^ T.card *
        (((r : ℝ) / Fintype.card V) ^ T.card) := by
      apply Finset.sum_le_sum
      intro T _
      exact mul_le_mul_of_nonneg_left (fixedSubset_joint_inclusion_le hr T)
        (pow_nonneg (sub_nonneg.mpr hq) _)
    _ = ∑ T ∈ A.powerset, ∏ _x ∈ T, (((r : ℝ) / Fintype.card V) * (q - 1)) := by
      apply Finset.sum_congr rfl
      intro T _
      simp only [Finset.prod_const, mul_pow]
      ring
    _ = _ := by rw [← Finset.prod_one_add]; simp

theorem intersection_complement_power {V : Type*} [Fintype V]
    (A S : Finset V) {q : ℝ} (hq : q ≠ 0) :
    q ^ (A ∩ Sᶜ).card = q ^ A.card * (q⁻¹) ^ (A ∩ S).card := by
  have hc : (A ∩ Sᶜ).card + (A ∩ S).card = A.card := by
    rw [← Finset.sdiff_eq_inter_compl]
    exact Finset.card_sdiff_add_card_inter A S
  rw [← hc, pow_add]
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow, mul_one]

theorem fixedSubset_power_bound
    {V : Type*} [Fintype V] {r : ℕ} [Nonempty (FixedSubset V r)]
    (hr : r ≤ Fintype.card V) (A : Finset V) {q : ℝ} (hq : 0 < q) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation (fun S => q ^ (A ∩ S.1).card) ≤
      (1 + ((r : ℝ) / Fintype.card V) * (q - 1)) ^ A.card := by
  by_cases hge : 1 ≤ q
  · exact fixedSubset_power_bound_ge_one hr A hge
  by_cases hn : Fintype.card V = 0
  · have hA : A = ∅ := Finset.card_eq_zero.mp (by have := A.card_le_univ; omega)
    simp only [hA, Finset.empty_inter, Finset.card_empty, pow_zero,
      FiniteLaw.expectation, mul_one, FiniteLaw.total, le_refl]
  have hnreal : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  let : Nonempty (FixedSubset V (Fintype.card V - r)) :=
    fixedSubset_nonempty (Nat.sub_le _ _)
  let e := fixedSubsetComplEquiv (V := V) hr
  have he : (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => q ^ (A ∩ S.1).card) =
      (FiniteLaw.uniform (FixedSubset V (Fintype.card V - r))).expectation
        (fun S => q ^ A.card * (q⁻¹) ^ (A ∩ S.1).card) := by
    rw [← finiteLaw_uniform_map_equiv e.symm, finiteLaw_map_expectation]
    apply Finset.sum_congr rfl
    intro S _
    congr 1
    exact intersection_complement_power A S.1 hq.ne'
  have hinv : 1 ≤ q⁻¹ := (one_le_inv₀ hq).mpr (le_of_not_ge hge)
  have hbase : q * (1 + (((Fintype.card V - r : ℕ) : ℝ) / Fintype.card V) * (q⁻¹ - 1)) =
      1 + ((r : ℝ) / Fintype.card V) * (q - 1) := by
    rw [Nat.cast_sub hr]
    field_simp
    ring
  rw [he]
  calc
    _ = q ^ A.card * (FiniteLaw.uniform (FixedSubset V (Fintype.card V - r))).expectation
        (fun S => (q⁻¹) ^ (A ∩ S.1).card) := by
      simp only [FiniteLaw.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ ≤ q ^ A.card *
        (1 + (((Fintype.card V - r : ℕ) : ℝ) / Fintype.card V) * (q⁻¹ - 1)) ^ A.card :=
      mul_le_mul_of_nonneg_left (fixedSubset_power_bound_ge_one (Nat.sub_le _ _) A hinv)
        (pow_nonneg hq.le _)
    _ = _ := by rw [← mul_pow, hbase]

end Oberwolfach
