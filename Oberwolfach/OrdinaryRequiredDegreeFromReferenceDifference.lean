module

public import Oberwolfach.OrdinaryForbiddenRequiredEditDegree

@[expose] public section
/-! Separate required-edge demand from deletion of the protected region:
only the edit and the sample/reference discrepancy can create a new
required edge inside that region. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_required_degree_from_reference_difference
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Bad:SimpleGraph V) (Inner:Finset V) (edit diff forbidden:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)
    (hDiff:∀v,((Sample\Reference).degree v:ℝ)≤diff)
    (hBad:∀v,(Bad.degree v:ℝ)≤forbidden):
    ∀v,((ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree v:ℝ)≤edit+diff+forbidden :=by
  have hsub:ordinaryForbiddenRequired Target Sample Reference Bad Inner≤(Target\Sample)⊔(Sample\Reference)⊔Bad:=by
    intro x y h
    change (ordinaryProtectedRequired Target Sample Reference Inner).Adj x y ∨ (Target⊓Bad).Adj x y at h
    rcases h with h|h
    · change (Target\Sample).Adj x y ∨ (spanningRestriction (Target\Reference) Inner).Adj x y at h
      rcases h with h|h
      · exact Or.inl (Or.inl h)
      · have hh:=(spanningRestriction_adj (Target\Reference) Inner x y).mp h
        by_cases hs:Sample.Adj x y
        · exact Or.inl (Or.inr ⟨hs,hh.1.2⟩)
        · exact Or.inl (Or.inl ⟨hh.1.1,hs⟩)
    · exact Or.inr h.2
  have hAdded:=added_graph_degree_le_symmetric_edit Target Sample edit hEdit
  intro v
  have h0:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have h1:=graph_degree_sup_le (Target\Sample) (Sample\Reference) v
  have h2:=graph_degree_sup_le ((Target\Sample)⊔(Sample\Reference)) Bad v
  have h0':((ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree v:ℝ)≤
      (((Target\Sample)⊔(Sample\Reference)⊔Bad).degree v:ℝ):=by exact_mod_cast h0
  have h1':(((Target\Sample)⊔(Sample\Reference)).degree v:ℝ)≤
      ((Target\Sample).degree v:ℝ)+((Sample\Reference).degree v:ℝ):=by
    have hh:((Target\Sample)⊔(Sample\Reference)).degree v≤(Target\Sample).degree v+(Sample\Reference).degree v:=by
      convert h1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  have h2':((((Target\Sample)⊔(Sample\Reference))⊔Bad).degree v:ℝ)≤
      (((Target\Sample)⊔(Sample\Reference)).degree v:ℝ)+Bad.degree v:=by
    have hh:(((Target\Sample)⊔(Sample\Reference))⊔Bad).degree v≤
        ((Target\Sample)⊔(Sample\Reference)).degree v+Bad.degree v:=by
      convert h2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  linarith [hAdded v,hDiff v,hBad v]
end Oberwolfach
