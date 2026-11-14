module

public import Oberwolfach.BipartiteRegularization
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! The graph represented by a bipartite zero-one matrix has two disjoint
copies of its label type as vertex classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bipartiteMatrixGraph {V : Type*} (M : V → V → ℕ) : SimpleGraph (V ⊕ V) where
  Adj
    | Sum.inl x, Sum.inr y => 0 < M x y
    | Sum.inr y, Sum.inl x => 0 < M x y
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

theorem bipartiteMatrixGraph_left_degree {V : Type*} [Fintype V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1) (x : V) :
    (bipartiteMatrixGraph M).degree (Sum.inl x) = ∑ y, M x y := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp only [bipartiteMatrixGraph, ite_false, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro y _
  have h := hM x y
  split_ifs <;> omega

theorem bipartiteMatrixGraph_right_degree {V : Type*} [Fintype V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1) (y : V) :
    (bipartiteMatrixGraph M).degree (Sum.inr y) = ∑ x, M x y := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp only [bipartiteMatrixGraph, ite_false, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  have h := hM x y
  split_ifs <;> omega

theorem retainedBipartiteGraph_le {V : Type*}
    (M : V → V → ℕ) (D : BipartiteEdges M → Bool) :
    bipartiteMatrixGraph (retainedBipartiteMatrix M D) ≤ bipartiteMatrixGraph M := by
  intro u v h
  cases u <;> cases v
  · exact h
  · exact lt_of_lt_of_le h (retainedBipartiteMatrix_le M D _ _)
  · exact lt_of_lt_of_le h (retainedBipartiteMatrix_le M D _ _)
  · exact h

theorem retainedBipartiteGraph_regular {V : Type*} [Fintype V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1)
    (D : BipartiteEdges M → Bool) (k : ℕ)
    (hl : ∀ x, ∑ y, retainedBipartiteMatrix M D x y = k)
    (hr : ∀ y, ∑ x, retainedBipartiteMatrix M D x y = k) :
    (bipartiteMatrixGraph (retainedBipartiteMatrix M D)).IsRegularOfDegree k := by
  intro v
  cases v with
  | inl x =>
    rw [bipartiteMatrixGraph_left_degree _
      (fun x y => (retainedBipartiteMatrix_le M D x y).trans (hM x y)), hl]
  | inr y =>
    rw [bipartiteMatrixGraph_right_degree _
      (fun x y => (retainedBipartiteMatrix_le M D x y).trans (hM x y)), hr]

theorem retainedBipartiteGraph_deleted_edge {V : Type*}
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1)
    (D : BipartiteEdges M → Bool) (e : BipartiteEdges M) :
    ¬ (bipartiteMatrixGraph (retainedBipartiteMatrix M D)).Adj
      (Sum.inl e.1) (Sum.inr e.2.1) ↔ D e = true := by
  change ¬ 0 < retainedBipartiteMatrix M D e.1 e.2.1 ↔ _
  rw [Nat.not_lt, Nat.le_zero]
  exact retainedBipartiteMatrix_edge M hM D e

end Oberwolfach
