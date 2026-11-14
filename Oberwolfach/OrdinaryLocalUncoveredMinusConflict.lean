module

public import Oberwolfach.OrdinaryLocalStateDegree

@[expose] public section
/-! Removing the conflict graph from the reference adds at most its local
degree to the unmatched sample/reference discrepancy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_uncovered_minus_conflict
    {V:Type} [Fintype V] [DecidableEq V]
    (Sample Reference Bad Used:SimpleGraph V) (Inner:Finset V) (x:V):
    ((spanningRestriction ((Sample\(Reference\Bad))\Used) Inner).degree x:ℝ)≤
      (spanningRestriction ((Sample\Reference)\Used) Inner).degree x+
      (spanningRestriction Bad Inner).degree x :=by
  have hsub:spanningRestriction ((Sample\(Reference\Bad))\Used) Inner≤
      spanningRestriction ((Sample\Reference)\Used) Inner⊔spanningRestriction Bad Inner:=by
    intro v w h
    have hh:=(spanningRestriction_adj ((Sample\(Reference\Bad))\Used) Inner v w).mp h
    by_cases hr:Reference.Adj v w
    · have hb:Bad.Adj v w:=by
        by_contra hbad
        exact hh.1.1.2 ⟨hr,hbad⟩
      exact Or.inr ((spanningRestriction_adj Bad Inner v w).mpr ⟨hb,hh.2.1,hh.2.2⟩)
    · exact Or.inl ((spanningRestriction_adj ((Sample\Reference)\Used) Inner v w).mpr
        ⟨⟨⟨hh.1.1.1,hr⟩,hh.1.2⟩,hh.2.1,hh.2.2⟩)
  have hdeg:=SimpleGraph.degree_le_of_le hsub (v:=x)
  have hsum:=graph_degree_sup_le (spanningRestriction ((Sample\Reference)\Used) Inner) (spanningRestriction Bad Inner) x
  have hsum':(spanningRestriction ((Sample\Reference)\Used) Inner⊔spanningRestriction Bad Inner).degree x≤
      (spanningRestriction ((Sample\Reference)\Used) Inner).degree x+(spanningRestriction Bad Inner).degree x:=by
    convert hsum using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  exact_mod_cast hdeg.trans hsum'
end Oberwolfach
