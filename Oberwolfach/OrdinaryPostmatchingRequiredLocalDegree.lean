module

public import Oberwolfach.OrdinaryPostmatchingRequired

@[expose] public section
/-! The post-matching forced demand only sees unmatched nonreference
sample edges inside the protected region. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_postmatching_required_local_degree
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Bad Used:SimpleGraph V) (Inner:Finset V) (edit localLoss forbidden:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)
    (hLocal:∀v,((spanningRestriction ((Sample\Reference)\Used) Inner).degree v:ℝ)≤localLoss)
    (hBad:∀v,(Bad.degree v:ℝ)≤forbidden):
    ∀v,((ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner).degree v:ℝ)≤edit+localLoss+forbidden :=by
  have hsub:ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner≤
      (Target\Sample)⊔(spanningRestriction ((Sample\Reference)\Used) Inner)⊔Bad:=by
    intro v w h
    have hnot:¬Used.Adj v w:=h.2
    rcases h.1 with h|h
    · rcases h with h|h
      · exact Or.inl (Or.inl h)
      · have hh:=(spanningRestriction_adj (Target\Reference) Inner v w).mp h
        by_cases hs:Sample.Adj v w
        · exact Or.inl (Or.inr ((spanningRestriction_adj ((Sample\Reference)\Used) Inner v w).mpr
            ⟨⟨⟨hs,hh.1.2⟩,hnot⟩,hh.2.1,hh.2.2⟩))
        · exact Or.inl (Or.inl ⟨hh.1.1,hs⟩)
    · exact Or.inr h.2
  have hAdded:=added_graph_degree_le_symmetric_edit Target Sample edit hEdit
  intro v
  have h0:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have h1:=graph_degree_sup_le (Target\Sample) (spanningRestriction ((Sample\Reference)\Used) Inner) v
  have h2:=graph_degree_sup_le ((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner) Bad v
  have h0':((ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner).degree v:ℝ)≤
      (((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner⊔Bad).degree v:ℝ):=by exact_mod_cast h0
  have h1':(((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner).degree v:ℝ)≤
      ((Target\Sample).degree v:ℝ)+(spanningRestriction ((Sample\Reference)\Used) Inner).degree v:=by
    have hh:((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner).degree v≤
        (Target\Sample).degree v+(spanningRestriction ((Sample\Reference)\Used) Inner).degree v:=by
      convert h1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  have h2':((((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner)⊔Bad).degree v:ℝ)≤
      (((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner).degree v:ℝ)+Bad.degree v:=by
    have hh:(((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner)⊔Bad).degree v≤
        ((Target\Sample)⊔spanningRestriction ((Sample\Reference)\Used) Inner).degree v+Bad.degree v:=by
      convert h2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  linarith [hAdded v,hLocal v,hBad v]
end Oberwolfach
