module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Inducing on a set containing all non-isolated vertices preserves edge count. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V:Type} [Fintype V] [DecidableEq V]

theorem graph_induce_edge_count_of_isolated_outside_set (Q:SimpleGraph V)
    [DecidableRel Q.Adj] (S:Set V) [DecidablePred (·∈S)]
    (hisol:∀ x,x∉S→∀ y,¬Q.Adj x y):
    (Q.induce S).edgeFinset.card=Q.edgeFinset.card := by
  have hsupport : Q.support ⊆ S := by
    intro x hx
    by_contra h
    obtain ⟨y,hxy⟩:=Q.mem_support.mp hx
    exact hisol x h y hxy
  exact Q.card_edgeFinset_induce_of_support_subset hsupport
end Oberwolfach
