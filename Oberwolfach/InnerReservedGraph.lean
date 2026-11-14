module

public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Preserve every inner edge that has not been designated as required. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem inner_reserved_graph_bounds
    {V:Type} [Fintype V] [DecidableEq V]
    (P Kbad:SimpleGraph V) (I:Finset V):
    let Jbad:=spanningRestriction P I\Kbad
    (∀v,(Jbad.degree v:ℝ)≤I.card) ∧ Disjoint Kbad.edgeFinset Jbad.edgeFinset:=by
  intro Jbad
  constructor
  · intro v
    have hsub:Jbad.neighborFinset v⊆I:=by
      intro w hw
      have hh:=(Jbad.mem_neighborFinset v w).mp hw
      have hi: (spanningRestriction P I).Adj v w:=hh.1
      exact ((spanningRestriction_adj _ _ _ _).mp hi).2.2
    have hh:=Finset.card_le_card hsub
    change Jbad.degree v≤I.card at hh
    exact_mod_cast hh
  · apply Finset.disjoint_left.mpr
    intro e he hj
    induction e using Sym2.ind with
    | _ x y =>
      have hk:Kbad.Adj x y:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
      have hj':Jbad.Adj x y:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hj
      exact hj'.2 hk

theorem inner_available_reserved_graph_bounds
    {V:Type} [Fintype V] [DecidableEq V]
    (P Used Kbad:SimpleGraph V) (I:Finset V):
    let Jbad:=spanningRestriction (P\Used) I\Kbad
    (∀v,(Jbad.degree v:ℝ)≤I.card) ∧ Disjoint Kbad.edgeFinset Jbad.edgeFinset ∧
      Disjoint Used.edgeFinset Jbad.edgeFinset:=by
  intro Jbad
  obtain ⟨hdegree,hK⟩:=inner_reserved_graph_bounds (P\Used) Kbad I
  refine ⟨hdegree,hK,?_⟩
  apply Finset.disjoint_left.mpr
  intro e he hj
  induction e using Sym2.ind with
  | _ x y =>
    have hu:Used.Adj x y:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
    have hj':Jbad.Adj x y:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hj
    exact ((spanningRestriction_adj _ _ _ _).mp hj'.1).1.2 hu

theorem inner_available_reserved_graph_at_host_scale
    {n:ℕ} (P Used Kbad:SimpleGraph (Fin n)) (I:Finset (Fin n)) (δ:ℝ)
    (hI:(I.card:ℝ)≤δ*n):
    let Jbad:=spanningRestriction (P\Used) I\Kbad
    (∀v,(Jbad.degree v:ℝ)≤δ*n) ∧ Disjoint Kbad.edgeFinset Jbad.edgeFinset ∧
      Disjoint Used.edgeFinset Jbad.edgeFinset:=by
  intro Jbad
  obtain ⟨hdegree,hK,hUsed⟩:=inner_available_reserved_graph_bounds P Used Kbad I
  exact ⟨fun v=>(hdegree v).trans hI,hK,hUsed⟩
end Oberwolfach
