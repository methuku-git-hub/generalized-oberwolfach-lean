module

public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section

/-! The permutation conflict graph has maximum degree at most 2b;
the equality case in the closed-distance relation is removed explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem permutationConflictGraph_degree_le {V : Type} [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (b : ℕ) (x : V) : (permutationConflictGraph π b).degree x≤2*b := by
  let S := Finset.univ.filter (fun y=>PermutationClose π b x y)
  have hx : x∉(permutationConflictGraph π b).neighborFinset x := by simp
  have hsub : insert x ((permutationConflictGraph π b).neighborFinset x)⊆S := by
    intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact Or.inl rfl
    · exact (((permutationConflictGraph π b).mem_neighborFinset x y).mp hy).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hx,SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hb := permutationClose_neighbour_card π b x
  have he : S.card=Fintype.card {y // PermutationClose π b x y} := by
    simp only [S,Fintype.card_subtype]
  rw [he] at hc
  omega

end Oberwolfach
