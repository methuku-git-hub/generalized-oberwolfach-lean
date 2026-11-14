module

public import Oberwolfach.GraphDifferenceChangedDegree

@[expose] public section
/-! A symmetric neighborhood edit bounds both directed graph differences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_graph_changes_degree (R Q:SimpleGraph V) (L:ℝ)
    (h:∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L):
    (∀v,((R\Q).degree v:ℝ)≤L) ∧ (∀v,((Q\R).degree v:ℝ)≤L):=by
  classical
  constructor
  · intro v
    have hh:=graph_difference_degree_le_changed R Q v
    have hs:changed (Q.neighborFinset v) (R.neighborFinset v)=changed (R.neighborFinset v) (Q.neighborFinset v):=by
      ext x
      simp only [changed,Finset.mem_union,Finset.mem_sdiff]
      tauto
    rw [hs] at hh
    have hi:(R\Q).degree v≤(changed (R.neighborFinset v) (Q.neighborFinset v)).card:=by
      convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    exact (Nat.cast_le.mpr hi).trans (h v)
  · intro v
    have hh:=graph_difference_degree_le_changed Q R v
    have hi:(Q\R).degree v≤(changed (R.neighborFinset v) (Q.neighborFinset v)).card:=by
      convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    exact (Nat.cast_le.mpr hi).trans (h v)
end Oberwolfach
