module

public import Oberwolfach.BipartiteRegularization
public import Oberwolfach.FiniteSamplingMeasure

@[expose] public section

/-! Simultaneous regularization of finitely many interfaces. The deletion
law is the independent product of the laws proved for the individual
interfaces. The common retained degree is fixed before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_coordinate_event {I : Type*} [Fintype I] [DecidableEq I]
    {State : I → Type*} [∀ i, Fintype (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (i : I) (A : State i → Prop) :
    (FiniteLaw.pi μ).probability (fun s => A (s i)) = (μ i).probability A := by
  let : ∀ i, MeasurableSpace (State i) := fun _ => ⊤
  let : ∀ i, MeasurableSingletonClass (State i) := fun _ => ⟨fun _ => trivial⟩
  have h := finiteLaw_coordinate_expectation μ i (fun x => if A x then (1 : ℝ) else 0)
  simpa only [FiniteLaw.expectation, FiniteLaw.probability, mul_ite, mul_one, mul_zero] using h

theorem finiteLaw_pi_positive_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    {State : I → Type*} [∀ i, Fintype (State i)]
    (μ : ∀ i, FiniteLaw (State i)) (s : ∀ i, State i)
    (hs : 0 < (FiniteLaw.pi μ).mass s) (i : I) : 0 < (μ i).mass (s i) := by
  by_contra hn
  have hz := le_antisymm (not_lt.mp hn) ((μ i).nonneg _)
  have hp : (FiniteLaw.pi μ).mass s = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz
  linarith

theorem interface_family_random_regularization (β : ℝ) (hβ : 0 < β) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ m₀ : ℕ, ∀ (I V : Type) [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V],
      m₀ ≤ Fintype.card V → ∀ (M : I → V → V → ℕ),
      (∀ i x y, M i x y ≤ 1) → ∀ d : ℝ,
      (∀ i x, (1 / 2 + β) * Fintype.card V ≤ ((∑ y, M i x y : ℕ) : ℝ)) →
      (∀ i y, (1 / 2 + β) * Fintype.card V ≤ ((∑ x, M i x y : ℕ) : ℝ)) →
      (∀ i x, d - η * Fintype.card V ≤ ((∑ y, M i x y : ℕ) : ℝ) ∧
        ((∑ y, M i x y : ℕ) : ℝ) ≤ d + η * Fintype.card V) →
      (∀ i y, d - η * Fintype.card V ≤ ((∑ x, M i x y : ℕ) : ℝ) ∧
        ((∑ x, M i x y : ℕ) : ℝ) ≤ d + η * Fintype.card V) →
      let q := ⌊d - Real.sqrt η * Fintype.card V⌋₊
      ∃ ν : FiniteLaw (∀ i, BipartiteEdges (M i) → Bool),
        (∀ D, 0 < ν.mass D → ∀ i,
          (∀ x, (∑ y, retainedBipartiteMatrix (M i) (D i) x y) = q) ∧
          (∀ y, (∑ x, retainedBipartiteMatrix (M i) (D i) x y) = q)) ∧
        (∀ (D : ∀ i, BipartiteEdges (M i) → Bool) i x y, retainedBipartiteMatrix (M i) (D i) x y ≤ M i x y) ∧
        (∀ i (e : BipartiteEdges (M i)),
          ν.probability (fun D => retainedBipartiteMatrix (M i) (D i) e.1 e.2.1 = 0) ≤
            C * Real.sqrt η) := by
  obtain ⟨C, η₀, hC, hη₀, hall⟩ := bipartite_matrix_random_regularization β hβ
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro η hη hηsmall
  obtain ⟨m₀, hm₀⟩ := hall η hη hηsmall
  refine ⟨m₀, ?_⟩
  intro I V _ _ _ _ hm M hM d hl hr hnl hnr
  have hex (i : I) := hm₀ V hm (M i) (hM i) d (hl i) (hr i) (hnl i) (hnr i)
  choose μ hdegrees hsub hprob using hex
  refine ⟨FiniteLaw.pi μ, ?_, ?_, ?_⟩
  · intro D hD i
    exact hdegrees i (D i) (finiteLaw_pi_positive_coordinates μ D hD i)
  · intro D i x y
    exact hsub i (D i) x y
  · intro i e
    rw [finiteLaw_pi_coordinate_event μ i (fun D => retainedBipartiteMatrix (M i) D e.1 e.2.1 = 0)]
    exact hprob i e

end Oberwolfach
