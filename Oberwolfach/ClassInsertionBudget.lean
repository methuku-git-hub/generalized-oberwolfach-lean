module

public import Oberwolfach.ClassRequiredGraphEditBounds
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! The regularisation insertions spend at most their incident edit budget,
including in the total-edge count. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem class_insertion_degree_le_edits
    {V:Type} [Fintype V] [DecidableEq V] (S₀ S:SimpleGraph V) (I:Finset V) (v:V):
    (spanningRestriction (S\S₀) I).degree v ≤
      (changed (S₀.neighborFinset v) (S.neighborFinset v)).card:=by
  apply Finset.card_le_card
  intro w hw
  have h:=(spanningRestriction_adj _ _ _ _).mp ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)
  simp [changed,SimpleGraph.mem_neighborFinset,h.1.1,h.1.2]

theorem class_insertion_edge_budget
    {V:Type} [Fintype V] [DecidableEq V] (S₀ S:SimpleGraph V) (I:Finset V) (b:ℝ)
    (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤b):
    (∀v,((spanningRestriction (S\S₀) I).degree v:ℝ)≤b) ∧
      2*((spanningRestriction (S\S₀) I).edgeFinset.card:ℝ)≤b*Fintype.card V:=by
  let E:=spanningRestriction (S\S₀) I
  have hd:∀v,(E.degree v:ℝ)≤b:=by
    intro v
    have hh:((E.degree v:ℝ)≤(changed (S₀.neighborFinset v) (S.neighborFinset v)).card):=by
      exact_mod_cast class_insertion_degree_le_edits S₀ S I v
    exact hh.trans (hedit v)
  refine ⟨hd,?_⟩
  have hs:(∑v:V,(E.degree v:ℝ))≤∑_v:V,b:=Finset.sum_le_sum (by intro v hv;exact hd v)
  have he:(∑v:V,(E.degree v:ℝ))=2*(E.edgeFinset.card:ℝ):=by
    rw [←Nat.cast_sum,E.sum_degrees_eq_twice_card_edges]
    push_cast
    ring
  rw [he] at hs
  simpa [mul_comm] using hs
end Oberwolfach
