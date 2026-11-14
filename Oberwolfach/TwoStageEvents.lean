module

public import Oberwolfach.FiniteUniform
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Event probabilities for sampling a partition first and a dependent
finite realization afterward. The second law may depend on the partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_probability {Ω : Type*} [Fintype Ω]
    {Γ : Ω → Type*} [∀ ω, Fintype (Γ ω)]
    (μ : FiniteLaw Ω) (ν : ∀ ω, FiniteLaw (Γ ω)) (A : (Σ ω, Γ ω) → Prop) :
    (μ.sigma ν).probability A =
      μ.expectation (fun ω => (ν ω).probability (fun γ => A ⟨ω, γ⟩)) := by
  unfold FiniteLaw.probability FiniteLaw.expectation
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  change (if A ⟨ω, γ⟩ then μ.mass ω * (ν ω).mass γ else 0) = _
  split_ifs <;> simp

theorem finiteLaw_twoStage_survival {Ω : Type*} [Fintype Ω]
    {Γ : Ω → Type*} [∀ ω, Fintype (Γ ω)]
    (μ : FiniteLaw Ω) (ν : ∀ ω, FiniteLaw (Γ ω))
    (E : Ω → Prop) (S : ∀ ω, Γ ω → Prop) (ε : ℝ)
    (h : ∀ ω, E ω → 1 - ε ≤ (ν ω).probability (S ω)) :
    (1 - ε) * μ.probability E ≤
      (μ.sigma ν).probability (fun z => E z.1 ∧ S z.1 z.2) := by
  rw [finiteLaw_sigma_probability]
  unfold FiniteLaw.expectation FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω
  · simp only [hE, ite_true, true_and]
    convert mul_le_mul_of_nonneg_right (h ω hE) (μ.nonneg ω) using 1 <;>
      simp only [FiniteLaw.probability] <;> ring
  · simp [hE]

theorem finiteLaw_avoid_deletions {E : Type*} [Fintype E] [DecidableEq E]
    (ν : FiniteLaw (E → Bool)) (F : Finset E) (p : ℝ)
    (hp : ∀ e ∈ F, ν.probability (fun D => D e = true) ≤ p) :
    1 - F.card * p ≤ ν.probability (fun D => ∀ e ∈ F, D e = false) := by
  have h := finiteLaw_common_event_lower ν F (fun e D => D e = true) (fun _ => p) hp
  simpa only [Bool.not_eq_true, Finset.sum_const, nsmul_eq_mul] using h

end Oberwolfach
