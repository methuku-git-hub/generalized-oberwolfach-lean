module

public import Oberwolfach.OrdinaryForbiddenRequiredEditDegree

@[expose] public section
/-! First match approximate-layer edges without deleting the whole protected
region. Afterwards require only the edges not already covered by that same
matching. This is a deterministic reduction; placement remains to be proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryPostmatchingRequired {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Bad Used:SimpleGraph V) (Inner:Finset V):SimpleGraph V:=
  ordinaryForbiddenRequired Target Sample Reference Bad Inner\Used

theorem ordinary_postmatching_required_relations
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Protect Bad Used:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hBad:Disjoint Reference Bad):
    let G:=ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner;
    G≤Target\Protect ∧ Disjoint G Used ∧
    ordinaryForbiddenRequired Target Sample Reference Bad Inner≤Used⊔G ∧
    (Target\Sample)≤Used⊔G ∧ Target⊓Bad≤Used⊔G ∧
    (∀v∈Inner,∀w∈Inner,Target.Adj v w→¬Reference.Adj v w→(Used⊔G).Adj v w) :=by
  intro G
  have hRel:=ordinary_forbidden_required_relations Target Sample Reference Protect Bad Inner hRef hProtect hBad
  have hG:G≤Target\Protect:=sdiff_le.trans hRel.1
  have hdis:Disjoint G Used:=by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact h.1.2 h.2
  have hcov:ordinaryForbiddenRequired Target Sample Reference Bad Inner≤Used⊔G:=by
    intro v w h
    by_cases hu:Used.Adj v w
    · exact Or.inl hu
    · exact Or.inr ⟨h,hu⟩
  refine ⟨hG,hdis,hcov,?_,hRel.2.2.2.1.trans hcov,?_⟩
  · intro v w h
    apply hcov
    exact Or.inl (Or.inl h)
  · intro v hv w hw hTarget hnot
    apply hcov
    exact Or.inl (Or.inr ((spanningRestriction_adj (Target\Reference) Inner v w).mpr ⟨⟨hTarget,hnot⟩,hv,hw⟩))

theorem ordinary_postmatching_required_degree
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Bad Used:SimpleGraph V) (Inner:Finset V) (edit uncovered:ℝ)
    (hRef:Reference≤Sample) (hBad:Disjoint Reference Bad)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)
    (hUncovered:∀v,(((Sample\Reference)\Used).degree v:ℝ)≤uncovered):
    ∀v,((ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner).degree v:ℝ)≤edit+uncovered :=by
  have hsub:ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner≤(Target\Sample)⊔((Sample\Reference)\Used):=by
    intro v w h
    have hnotused:¬Used.Adj v w:=h.2
    have hG:=h.1
    have htarget:Target.Adj v w:=by
      rcases hG with hG|hG
      · rcases hG with hG|hG
        · exact hG.1
        · exact ((spanningRestriction_adj (Target\Reference) Inner v w).mp hG).1.1
      · exact hG.1
    have hnoref:¬Reference.Adj v w:=by
      intro href
      rcases hG with hG|hG
      · rcases hG with hG|hG
        · exact hG.2 (hRef href)
        · exact ((spanningRestriction_adj (Target\Reference) Inner v w).mp hG).1.2 href
      · exact (disjoint_iff_inf_le.mp hBad) ⟨href,hG.2⟩
    by_cases hs:Sample.Adj v w
    · exact Or.inr ⟨⟨hs,hnoref⟩,hnotused⟩
    · exact Or.inl ⟨htarget,hs⟩
  have hAdded:=added_graph_degree_le_symmetric_edit Target Sample edit hEdit
  intro v
  have hdeg:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have hsum:=graph_degree_sup_le (Target\Sample) ((Sample\Reference)\Used) v
  have hdeg':((ordinaryPostmatchingRequired Target Sample Reference Bad Used Inner).degree v:ℝ)≤
      (((Target\Sample)⊔((Sample\Reference)\Used)).degree v:ℝ):=by exact_mod_cast hdeg
  have hsum':(((Target\Sample)⊔((Sample\Reference)\Used)).degree v:ℝ)≤
      ((Target\Sample).degree v:ℝ)+(((Sample\Reference)\Used).degree v:ℝ):=by
    have hh:((Target\Sample)⊔((Sample\Reference)\Used)).degree v≤
        (Target\Sample).degree v+((Sample\Reference)\Used).degree v:=by
      convert hsum using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  linarith [hAdded v,hUncovered v]
end Oberwolfach
