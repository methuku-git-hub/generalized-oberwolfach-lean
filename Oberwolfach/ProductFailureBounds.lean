module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! Combining a first sampling failure with a conditional second failure.
The original root event is retained in the joint probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_le_one' {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A : Ω → Prop) : μ.probability A≤1 := by
  have hc := finiteLaw_probability_compl μ A
  linarith [finiteLaw_probability_nonneg μ (fun ω => ¬A ω)]

theorem finiteLaw_prod_probability_slices {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (A : Ω → Γ → Prop) :
    (μ.prod ν).probability (fun z => A z.1 z.2)=
      ∑ ω,μ.mass ω*ν.probability (A ω) := by
  unfold FiniteLaw.probability
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  change (if A ω γ then μ.mass ω*ν.mass γ else 0)=
    μ.mass ω*(if A ω γ then ν.mass γ else 0)
  split_ifs <;> simp

theorem finiteLaw_product_rooted_failure {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (E A : Ω → Prop) (B : Ω → Γ → Prop)
    (b c : ℝ) (hc : 0≤c)
    (hA : μ.probability (fun ω => E ω ∧ A ω)≤b*μ.probability E)
    (hB : ∀ ω,¬A ω → ν.probability (B ω)≤c) :
    (μ.prod ν).probability (fun z => E z.1 ∧ B z.1 z.2)≤
      (b+c)*μ.probability E := by
  rw [finiteLaw_prod_probability_slices μ ν (fun ω γ => E ω ∧ B ω γ)]
  have hp (ω : Ω) : ν.probability (fun γ => E ω ∧ B ω γ)≤
      (if E ω ∧ A ω then 1 else 0)+c*(if E ω then 1 else 0) := by
    by_cases hE : E ω
    · by_cases hbad : A ω
      · simp only [hE,true_and,hbad,ite_true,mul_one]
        exact (finiteLaw_probability_le_one' ν (B ω)).trans (by linarith)
      · simp only [hE,true_and,hbad,ite_false,ite_true,zero_add,mul_one]
        exact hB ω hbad
    · simp [hE,FiniteLaw.probability]
  calc
    _ ≤ ∑ ω,μ.mass ω*((if E ω ∧ A ω then 1 else 0)+c*(if E ω then 1 else 0)) :=
      Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hp ω) (μ.nonneg ω))
    _ = μ.probability (fun ω => E ω ∧ A ω)+c*μ.probability E := by
      unfold FiniteLaw.probability
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hE : E ω <;> by_cases hbad : A ω <;> simp [hE,hbad] <;> ring
    _ ≤ _ := by nlinarith only [hA]

end Oberwolfach
