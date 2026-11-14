module

public import Oberwolfach.RegularizationComplement

@[expose] public section

/-! A sampled set of retained physical bipartite edges, represented by its
adjacency multiplicities. For a simple input these remain zero or one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def retainedBipartiteMatrix {V : Type*} (M : V → V → ℕ)
    (D : BipartiteEdges M → Bool) (x y : V) : ℕ :=
  ∑ t : Fin (M x y), if D ⟨x, y, t⟩ = false then 1 else 0

theorem retainedBipartiteMatrix_le {V : Type*}
    (M : V → V → ℕ) (D : BipartiteEdges M → Bool) (x y : V) :
    retainedBipartiteMatrix M D x y ≤ M x y := by
  calc
    _ ≤ ∑ _ : Fin (M x y), 1 := by
      apply Finset.sum_le_sum
      intro _ _
      split_ifs <;> omega
    _ = _ := by simp

theorem retainedBipartiteMatrix_row {V : Type*} [Fintype V]
    (M : V → V → ℕ) (D : BipartiteEdges M → Bool) (x : V) :
    (∑ y, retainedBipartiteMatrix M D x y) =
      ∑ e : BipartiteEdges M, if e.1 = x ∧ D e = false then (1 : ℕ) else 0 := by
  symm
  rw [Fintype.sum_sigma]
  have hsum (u : V) : (∑ e : (Σ y, Fin (M u y)),
      if u = x ∧ D ⟨u, e⟩ = false then (1 : ℕ) else 0) =
      if u = x then ∑ y, retainedBipartiteMatrix M D u y else 0 := by
    by_cases h : u = x
    · simp only [h, ite_true, true_and, Fintype.sum_sigma, retainedBipartiteMatrix]
    · simp [h]
  simp_rw [hsum]
  simp

theorem retainedBipartiteMatrix_column {V : Type*} [Fintype V]
    (M : V → V → ℕ) (D : BipartiteEdges M → Bool) (y : V) :
    (∑ x, retainedBipartiteMatrix M D x y) =
      ∑ e : BipartiteEdges M, if e.2.1 = y ∧ D e = false then (1 : ℕ) else 0 := by
  symm
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_sigma]
  have hsum (v : V) : (∑ t : Fin (M x v),
      if v = y ∧ D ⟨x, v, t⟩ = false then (1 : ℕ) else 0) =
      if v = y then retainedBipartiteMatrix M D x v else 0 := by
    by_cases h : v = y
    · simp only [h, ite_true, true_and, retainedBipartiteMatrix]
    · simp [h]
  simp_rw [hsum]
  simp

theorem retainedBipartiteMatrix_edge {V : Type*}
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1)
    (D : BipartiteEdges M → Bool) (e : BipartiteEdges M) :
    retainedBipartiteMatrix M D e.1 e.2.1 = 0 ↔ D e = true := by
  rcases e with ⟨x, y, t⟩
  have heq : M x y = 1 := by have ht := t.isLt; have hm := hM x y; omega
  have hs : retainedBipartiteMatrix M D x y =
      if D ⟨x, y, t⟩ = false then 1 else 0 := by
    unfold retainedBipartiteMatrix
    have hsub : Subsingleton (Fin (M x y)) := by rw [heq]; infer_instance
    letI := hsub
    rw [Finset.sum_eq_single t]
    · intro b _ hbt
      exact (hbt (Subsingleton.elim _ _)).elim
    · simp
  rw [hs]
  cases h : D ⟨x, y, t⟩ <;> simp

end Oberwolfach
