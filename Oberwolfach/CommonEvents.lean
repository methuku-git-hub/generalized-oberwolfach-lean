module

public import Oberwolfach.BoundedDifferences

@[expose] public section

/-!
Finite union bounds and simultaneous concentration. The test family is
fixed before the sample. No uniformity over arbitrary sample-dependent
domains is asserted.
-/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finiteLaw_probability_nonneg
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (A : Ω → Prop) :
    0 ≤ μ.probability A := by
  classical
  apply Finset.sum_nonneg
  intro ω _
  change 0 ≤ if A ω then μ.mass ω else 0
  split_ifs
  · exact μ.nonneg ω
  · exact le_refl _

theorem finiteLaw_probability_mono
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (A B : Ω → Prop)
    (h : ∀ ω, A ω → B ω) : μ.probability A ≤ μ.probability B := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  change (if A ω then μ.mass ω else 0) ≤ if B ω then μ.mass ω else 0
  by_cases ha : A ω
  · simp [ha, h ω ha]
  · simp only [ha, ite_false]
    split_ifs
    · exact μ.nonneg ω
    · exact le_refl _

theorem finiteLaw_probability_compl
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (A : Ω → Prop) :
    μ.probability A + μ.probability (fun ω => ¬ A ω) = 1 := by
  classical
  unfold FiniteLaw.probability
  rw [← Finset.sum_add_distrib, ← μ.total]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ha : A ω <;> simp [ha]

theorem finiteLaw_union_bound
    {Ω J : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Finset J) (A : J → Ω → Prop) :
    μ.probability (fun ω => ∃ j ∈ T, A j ω) ≤ ∑ j ∈ T, μ.probability (A j) := by
  classical
  unfold FiniteLaw.probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ j ∈ T, A j ω
  · obtain ⟨j, hj, ha⟩ := h
    simp only [show (∃ j ∈ T, A j ω) from ⟨j, hj, ha⟩, ite_true]
    have hh := Finset.single_le_sum (s := T)
      (f := fun j => if A j ω then μ.mass ω else 0)
      (fun j _ => by split_ifs; exact μ.nonneg ω; exact le_refl _) hj
    simpa [ha] using hh
  · simp only [h, ite_false]
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact μ.nonneg ω
    · exact le_refl _

theorem finiteLaw_common_event_lower
    {Ω J : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Finset J) (A : J → Ω → Prop) (p : J → ℝ)
    (h : ∀ j ∈ T, μ.probability (A j) ≤ p j) :
    1 - ∑ j ∈ T, p j ≤ μ.probability (fun ω => ∀ j ∈ T, ¬ A j ω) := by
  have hbad := (finiteLaw_union_bound μ T A).trans (Finset.sum_le_sum h)
  have hcomp := finiteLaw_probability_compl μ (fun ω => ∃ j ∈ T, A j ω)
  simp only [not_exists, not_and] at hcomp
  linarith

set_option backward.isDefEq.respectTransparency false in
theorem finiteLaw_common_event_exists
    {Ω J : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (T : Finset J) (A : J → Ω → Prop) (p : J → ℝ)
    (h : ∀ j ∈ T, μ.probability (A j) ≤ p j)
    (hsmall : ∑ j ∈ T, p j < 1) :
    ∃ ω, 0 < μ.mass ω ∧ ∀ j ∈ T, ¬ A j ω := by
  classical
  have hp : 0 < μ.probability (fun ω => ∀ j ∈ T, ¬ A j ω) :=
    (sub_pos.mpr hsmall).trans_le (finiteLaw_common_event_lower μ T A p h)
  have hn (ω : Ω) (_hω : ω ∈ Finset.univ) :
      0 ≤ (if ∀ j ∈ T, ¬ A j ω then μ.mass ω else 0) := by
    split_ifs
    · exact μ.nonneg ω
    · exact le_refl _
  have heq : μ.probability (fun ω => ∀ j ∈ T, ¬ A j ω) =
      ∑ ω, (if ∀ j ∈ T, ¬ A j ω then μ.mass ω else 0) := by
    unfold FiniteLaw.probability
    apply Finset.sum_congr rfl
    intro ω _
    exact (ite_eq_ite (∀ j ∈ T, ¬ A j ω) (μ.mass ω) 0).mpr trivial
  rw [heq] at hp
  have hp' := hp
  obtain ⟨ω, _, hω⟩ := (Finset.sum_pos_iff_of_nonneg hn).mp hp'
  split_ifs at hω with ha
  · exact ⟨ω, hω, ha⟩
  · exact (lt_irrefl _ hω).elim

/-- One event controls every fixed test. The formula retains each
individual influence bound and tolerance, and needs no independence
between the tests. -/
theorem finiteLaw_simultaneous_boundedDifferences
    {E J : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e, Fintype (State e)]
    (μ : ∀ e, FiniteLaw (State e)) (T : Finset J)
    (X : J → (∀ e, State e) → ℝ) (c : J → E → ℝ) (t : J → ℝ)
    (hc : ∀ j ∈ T, ∀ e, 0 ≤ c j e) (ht : ∀ j ∈ T, 0 ≤ t j)
    (hchange : ∀ j ∈ T, ∀ (e : E) (σ τ : ∀ i, State i),
      (∀ i, i ≠ e → σ i = τ i) → |X j σ - X j τ| ≤ c j e) :
    1 - (∑ j ∈ T, 2 * Real.exp (-2 * (t j) ^ 2 / (∑ e, (c j e) ^ 2))) ≤
      (FiniteLaw.pi μ).probability (fun σ =>
        ∀ j ∈ T, |X j σ - (FiniteLaw.pi μ).expectation (X j)| < t j) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) T
    (fun j σ => t j ≤ |X j σ - (FiniteLaw.pi μ).expectation (X j)|)
    (fun j => 2 * Real.exp (-2 * (t j) ^ 2 / (∑ e, (c j e) ^ 2)))
    (fun j hj => finiteLaw_boundedDifferences μ (X j) (c j) (hc j hj)
      (hchange j hj) (ht j hj))
  simpa only [not_le] using hh

end Oberwolfach
