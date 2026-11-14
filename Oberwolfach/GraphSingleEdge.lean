module

public import Oberwolfach.GraphDeletion
public import Mathlib.Combinatorics.SimpleGraph.Operations

@[expose] public section

/-! Exact degree loss when deleting a specified edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem single_edge_degree {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) (huv : u≠v) (x : V) :
    (SimpleGraph.edge u v).degree x=if x=u ∨ x=v then 1 else 0 := by
  by_cases hxu : x=u
  · subst x
    have he : (SimpleGraph.edge u v).neighborFinset u={v} := by
      ext y
      simp [SimpleGraph.edge_adj,huv,eq_comm]
      aesop
    rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
    simp
  · by_cases hxv : x=v
    · subst x
      have he : (SimpleGraph.edge u v).neighborFinset v={u} := by
        ext y
        simp [SimpleGraph.edge_adj,huv,eq_comm]
        aesop
      rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
      simp
    · have he : (SimpleGraph.edge u v).neighborFinset x=∅ := by
        ext y
        simp [SimpleGraph.edge_adj,hxu,hxv]
      rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
      simp [hxu,hxv]

theorem single_edge_deletion_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v) (x : V) :
    (G\SimpleGraph.edge u v).degree x+(if x=u ∨ x=v then 1 else 0)=G.degree x := by
  have hsub : SimpleGraph.edge u v≤G := (SimpleGraph.edge_le_iff G).mpr (Or.inr huv)
  have hd := graph_degree_sdiff G _ hsub x
  have hle : (SimpleGraph.edge u v).degree x≤G.degree x := SimpleGraph.degree_le_of_le hsub
  have he := single_edge_degree u v huv.ne x
  simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at he hle hd ⊢
  omega

end Oberwolfach
