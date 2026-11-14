module

public import Oberwolfach.UniformConditioning
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! Integrating estimates conditional on specified labels. The final
union bound ranges over positions, never over their possible labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_fibre_probability_bound {Ω Λ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Λ]
    (f : Ω → Λ) (A : Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ y (hy : Nonempty {ω : Ω // f ω=y}),
      letI := hy
      (FiniteLaw.uniform {ω : Ω // f ω=y}).probability (fun ω => A ω.val) ≤ ε) :
    (FiniteLaw.uniform Ω).probability A ≤ ε := by
  let μ := FiniteLaw.uniform Ω
  have hb (y : Λ) : μ.probability (fun ω => A ω ∧ f ω=y) ≤ μ.probability (fun ω => f ω=y)*ε := by
    by_cases hn : Nonempty {ω : Ω // f ω=y}
    · letI := hn
      have hh := uniform_probability_intersection (fun ω : Ω => f ω=y) A
      have he : (fun ω : Ω => A ω ∧ f ω=y)=(fun ω => f ω=y ∧ A ω) := by
        funext ω;exact propext and_comm
      rw [he]
      change (FiniteLaw.uniform Ω).probability _ ≤ _
      rw [hh]
      exact mul_le_mul_of_nonneg_left (h y hn) (finiteLaw_probability_nonneg _ _)
    · have hz : μ.probability (fun ω => A ω ∧ f ω=y)=0 := by
        unfold FiniteLaw.probability
        apply Finset.sum_eq_zero
        intro ω _
        have hne : f ω≠y := fun he => hn ⟨⟨ω,he⟩⟩
        simp [hne]
      rw [hz]
      exact mul_nonneg (finiteLaw_probability_nonneg _ _) hε
  have hsum : (∑ y,μ.probability (fun ω => f ω=y))=1 := by
    have hh := finiteLaw_probability_value_partition μ (fun _ => True) f
    have ht : μ.probability (fun _ => True)=1 := by simpa only [FiniteLaw.probability,ite_true] using μ.total
    simpa only [true_and,ht] using hh.symm
  calc
    _ = ∑ y,μ.probability (fun ω => A ω ∧ f ω=y) := finiteLaw_probability_value_partition μ A f
    _ ≤ ∑ y,μ.probability (fun ω => f ω=y)*ε := Finset.sum_le_sum (fun y _ => hb y)
    _ = ε := by rw [← Finset.sum_mul,hsum,one_mul]

theorem uniform_position_common_event {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    (tests : Finset J) {Λ : J → Type*} [∀ j,Fintype (Λ j)]
    (labels : ∀ j,Ω → Λ j) (Bad : J → Ω → Prop) (ε : J → ℝ)
    (hε : ∀ j∈tests,0 ≤ ε j)
    (h : ∀ j∈tests,∀ y (hy : Nonempty {ω : Ω // labels j ω=y}),
      letI := hy
      (FiniteLaw.uniform {ω : Ω // labels j ω=y}).probability (fun ω => Bad j ω.val) ≤ ε j) :
    1-∑ j∈tests,ε j ≤ (FiniteLaw.uniform Ω).probability (fun ω => ∀ j∈tests,¬Bad j ω) := by
  exact finiteLaw_common_event_lower _ tests Bad ε
    (fun j hj => uniform_fibre_probability_bound (labels j) (Bad j) (ε j) (hε j hj) (h j hj))

theorem uniform_position_common_exists {Ω J : Type*} [Fintype Ω] [Nonempty Ω]
    (tests : Finset J) {Λ : J → Type*} [∀ j,Fintype (Λ j)]
    (labels : ∀ j,Ω → Λ j) (Bad : J → Ω → Prop) (ε : J → ℝ)
    (hε : ∀ j∈tests,0 ≤ ε j)
    (h : ∀ j∈tests,∀ y (hy : Nonempty {ω : Ω // labels j ω=y}),
      letI := hy
      (FiniteLaw.uniform {ω : Ω // labels j ω=y}).probability (fun ω => Bad j ω.val) ≤ ε j)
    (hsmall : ∑ j∈tests,ε j < 1) :
    ∃ ω,∀ j∈tests,¬Bad j ω := by
  obtain ⟨ω,_,hω⟩ := finiteLaw_common_event_exists (FiniteLaw.uniform Ω) tests Bad ε
    (fun j hj => uniform_fibre_probability_bound (labels j) (Bad j) (ε j) (hε j hj) (h j hj)) hsmall
  exact ⟨ω,hω⟩

end Oberwolfach
