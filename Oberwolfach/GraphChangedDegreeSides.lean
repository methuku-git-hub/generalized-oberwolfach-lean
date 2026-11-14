module

public import Oberwolfach.GraphDifferenceChangedDegree

@[expose] public section
/-! The symmetric neighbourhood edit is bounded by the degrees of its two
one-sided graph differences. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_changed_degree_le_sides
    {V:Type} [Fintype V] [DecidableEq V] (A B:SimpleGraph V) (x:V):
    (changed (A.neighborFinset x) (B.neighborFinset x)).card≤(A\B).degree x+(B\A).degree x:=by
  have heq:changed (A.neighborFinset x) (B.neighborFinset x)=
      (A\B).neighborFinset x ∪ (B\A).neighborFinset x:=by
    ext y
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]
  rw [heq]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_union_le ((A\B).neighborFinset x) ((B\A).neighborFinset x)
end Oberwolfach
