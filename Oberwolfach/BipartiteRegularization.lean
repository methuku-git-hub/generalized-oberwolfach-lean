module

public import Oberwolfach.RetainedBipartiteMatrix

@[expose] public section

/-! Regularization with controlled edge-deletion probabilities, including
the constant and order quantifiers of the manuscript lemma. The sample D
specifies deleted edges; R is the actual retained adjacency matrix. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bipartite_matrix_random_regularization (β : ℝ) (hβ : 0 < β) :
    ∃ C η₀ : ℝ, 0 < C ∧ 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ m₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], m₀ ≤ Fintype.card V →
      ∀ (M : V → V → ℕ), (∀ x y, M x y ≤ 1) → ∀ d : ℝ,
      (∀ x, (1 / 2 + β) * Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ)) →
      (∀ y, (1 / 2 + β) * Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ)) →
      (∀ x, d - η * Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ) ∧
        ((∑ y, M x y : ℕ) : ℝ) ≤ d + η * Fintype.card V) →
      (∀ y, d - η * Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ) ∧
        ((∑ x, M x y : ℕ) : ℝ) ≤ d + η * Fintype.card V) →
      let k := ⌊d - Real.sqrt η * Fintype.card V⌋₊
      ∃ ν : FiniteLaw (BipartiteEdges M → Bool),
        (∀ D, 0 < ν.mass D →
          (∀ x, (∑ y, retainedBipartiteMatrix M D x y) = k) ∧
          (∀ y, (∑ x, retainedBipartiteMatrix M D x y) = k)) ∧
        (∀ D x y, retainedBipartiteMatrix M D x y ≤ M x y) ∧
        (∀ e : BipartiteEdges M,
          ν.probability (fun D => retainedBipartiteMatrix M D e.1 e.2.1 = 0) ≤
            C * Real.sqrt η) := by
  obtain ⟨C, η₀, hC, hη₀, hall⟩ := matrix_regularization_deletion_law β hβ
  refine ⟨C, η₀, hC, hη₀, ?_⟩
  intro η hη hsmall
  obtain ⟨m₀, hm₀⟩ := hall η hη hsmall
  refine ⟨m₀, ?_⟩
  intro V _ _ hm M hM d hl hr hnl hnr
  obtain ⟨hkl, hkr, ν, hdegrees, hprob⟩ := hm₀ V hm M hM d hl hr hnl hnr
  refine ⟨ν, ?_, retainedBipartiteMatrix_le M, ?_⟩
  · intro D hD
    obtain ⟨hdleft, hdright⟩ := hdegrees D hD
    constructor
    · intro x
      rw [retainedBipartiteMatrix_row]
      exact selected_complement_degree (fun e : BipartiteEdges M => e.1 = x)
        D _ _ (hkl x) (bipartiteEdges_row_degree M x) (by
          convert hdleft x using 1
          apply Finset.sum_congr rfl
          intro e _
          split_ifs <;> rfl)
    · intro y
      rw [retainedBipartiteMatrix_column]
      exact selected_complement_degree (fun e : BipartiteEdges M => e.2.1 = y)
        D _ _ (hkr y) (bipartiteEdges_column_degree M y) (by
          convert hdright y using 1
          apply Finset.sum_congr rfl
          intro e _
          split_ifs <;> rfl)
  · intro e
    convert hprob e using 1
    congr 1
    ext D
    exact retainedBipartiteMatrix_edge M hM D e

end Oberwolfach
