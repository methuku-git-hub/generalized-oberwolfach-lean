module

public import Oberwolfach.Neighbourhoods
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Removing forbidden edges from a reference can only reduce its symmetric
edit distance to a target that already avoids the forbidden graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_forbidden_reference_change_le (R Q F:SimpleGraph V)
    (hQ:Disjoint Q F) (v:V):
    (changed ((R\F).neighborFinset v) (Q.neighborFinset v)).card≤
      (changed (R.neighborFinset v) (Q.neighborFinset v)).card:=by
  apply Finset.card_le_card
  intro w hw
  simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj] at hw ⊢
  have hdis:¬(Q.Adj v w ∧ F.Adj v w):=fun hh=>(disjoint_iff_inf_le.mp hQ) hh
  tauto
end Oberwolfach
