module

public import Oberwolfach.AveragedDecompositions
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! The outer average uses one fixed good event. These inequalities keep
both its probability loss and the normalization visible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_expectation_indicator_value {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E : Ω → Prop) (k : ℝ) [DecidablePred E] :
    μ.expectation (fun ω => if E ω then k else 0) = k * μ.probability E := by
  unfold FiniteLaw.expectation FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h, mul_comm]

theorem averagedWeight_good_incidence_bounds {Ω T : Type*} [Fintype Ω] [Fintype T]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) (I : T → Prop) (E Good : Ω → Prop)
    (ρ δ L U : ℝ) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hgood : 1 - δ ≤ μ.probability Good)
    (hload : ∀ ω, (if E ω ∧ Good ω then L else 0) ≤ (∑ t, if I t then w ω t else 0) ∧
      (∑ t, if I t then w ω t else 0) ≤ (if E ω then U else 0)) :
    L * (μ.probability E - δ) / ρ ≤ (∑ t, if I t then averagedWeight μ w ρ t else 0) ∧
      (∑ t, if I t then averagedWeight μ w ρ t else 0) ≤ U * μ.probability E / ρ := by
  rw [averagedWeight_incidence]
  have hlo := finiteLaw_expectation_mono μ _ _ (fun ω => (hload ω).1)
  have hhi := finiteLaw_expectation_mono μ _ _ (fun ω => (hload ω).2)
  rw [finiteLaw_expectation_indicator_value μ (fun ω => E ω ∧ Good ω) L] at hlo
  rw [finiteLaw_expectation_indicator_value μ E U] at hhi
  constructor
  · exact div_le_div_of_nonneg_right
      ((mul_le_mul_of_nonneg_left (finiteLaw_good_intersection μ E Good δ hgood) hL).trans hlo) hρ.le
  · exact div_le_div_of_nonneg_right hhi hρ.le

theorem averagedWeight_good_edge_bounds {Ω T : Type*} [Fintype Ω] [Fintype T]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) (I : T → Prop) (E Good : Ω → Prop)
    (ρ δ p ε : ℝ) (hρ : 0 < ρ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 ≤ ε)
    (hprob : μ.probability E = ρ) (hgood : 1 - δ ≤ μ.probability Good)
    (hscale : δ ≤ ε * ρ)
    (hload : ∀ ω, (if E ω ∧ Good ω then 1 - p else 0) ≤ (∑ t, if I t then w ω t else 0) ∧
      (∑ t, if I t then w ω t else 0) ≤ (if E ω then 1 else 0)) :
    1 - p - ε ≤ (∑ t, if I t then averagedWeight μ w ρ t else 0) ∧
      (∑ t, if I t then averagedWeight μ w ρ t else 0) ≤ 1 := by
  obtain ⟨hl,hu⟩ := averagedWeight_good_incidence_bounds μ w I E Good ρ δ (1-p) 1 hρ
    (sub_nonneg.mpr hp1) hgood hload
  rw [hprob] at hl hu
  constructor
  · apply le_trans _ hl
    apply (le_div_iff₀ hρ).mpr
    have h := mul_le_mul_of_nonneg_left hscale (sub_nonneg.mpr hp1)
    nlinarith [mul_nonneg hp hε]
  · simpa only [one_mul, div_self hρ.ne'] using hu

theorem averagedWeight_zero_off_support {Ω T : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (w : Ω → T → ℝ) (ρ : ℝ) (S : T → Prop)
    (hs : ∀ ω t, ¬ S t → w ω t = 0) (t : T) (ht : ¬ S t) :
    averagedWeight μ w ρ t = 0 := by
  unfold averagedWeight FiniteLaw.expectation
  simp only [hs _ _ ht, mul_zero, Finset.sum_const_zero, zero_div]

end Oberwolfach
