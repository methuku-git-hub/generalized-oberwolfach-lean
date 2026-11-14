module

public import Oberwolfach.Neighbourhoods
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! One side of a graph edit is bounded by the symmetric neighbourhood edit. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_difference_degree_le_changed
    {V:Type} [Fintype V] [DecidableEq V] (S G:SimpleGraph V) (x:V):
    (S\G).degree x≤(changed (G.neighborFinset x) (S.neighborFinset x)).card:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj] at hy
  unfold changed
  simp only [Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset]
  exact Or.inr hy
end Oberwolfach
