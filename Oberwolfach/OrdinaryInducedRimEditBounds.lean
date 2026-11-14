module

public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! Symmetric ambient rim edits bound both directions of the induced-host
edit, without increasing the per-vertex loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem ordinary_induced_rim_difference_degree_le_changed
    (Q R : SimpleGraph V) (A : Set V) (x : A) :
    (((Q.induce A \ R.induce A).degree x) : ℝ) ≤
      ((changed (Q.neighborFinset x.val) (R.neighborFinset x.val)).card : ℝ) := by
  have hi : ((Q.induce A \ R.induce A).neighborFinset x).card ≤
      (changed (Q.neighborFinset x.val) (R.neighborFinset x.val)).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro y hy
      change y ∈ (Q.induce A \ R.induce A).neighborFinset x at hy
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.sdiff_adj, SimpleGraph.induce_adj] at hy
      change y.val ∈ changed (Q.neighborFinset x.val) (R.neighborFinset x.val)
      simp only [changed, Finset.mem_union, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
      exact Or.inl hy
    · intro a _ b _ h
      exact Subtype.val_injective h
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hi
  exact_mod_cast hi

theorem ordinary_induced_rim_edit_bounds
    (Q R : SimpleGraph V) (A : Set V) (L : ℝ)
    (h : ∀ x, ((changed (Q.neighborFinset x) (R.neighborFinset x)).card : ℝ) ≤ L) :
    (∀ x : A, (((Q.induce A \ R.induce A).degree x) : ℝ) ≤ L) ∧
    (∀ x : A, (((R.induce A \ Q.induce A).degree x) : ℝ) ≤ L) := by
  constructor
  · intro x
    exact (ordinary_induced_rim_difference_degree_le_changed Q R A x).trans (h x.val)
  · intro x
    have h' : ((changed (R.neighborFinset x.val) (Q.neighborFinset x.val)).card : ℝ) ≤ L := by
      simpa only [changed, Finset.union_comm] using h x.val
    exact (ordinary_induced_rim_difference_degree_le_changed R Q A x).trans h'
end Oberwolfach
