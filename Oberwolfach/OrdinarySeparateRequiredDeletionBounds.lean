module

public import Oberwolfach.OrdinaryRequiredDegreeFromReferenceDifference

@[expose] public section
/-! The forced-edge graph and the matching-deletion graph have different
costs: only the latter pays for the protected reference graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_separate_required_deletion_bounds
    {V:Type} [Fintype V] [DecidableEq V]
    (Target Sample Reference Protect Bad:SimpleGraph V) (Inner:Finset V) (edit diff protectRate forbidden:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)
    (hDiff:∀v,((Sample\Reference).degree v:ℝ)≤diff)
    (hProtect:∀v,(Protect.degree v:ℝ)≤protectRate)
    (hBad:∀v,(Bad.degree v:ℝ)≤forbidden):
    (∀v,((ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree v:ℝ)≤edit+diff+forbidden) ∧
    (∀v,((ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree v:ℝ)≤edit+protectRate+diff+forbidden) :=by
  refine ⟨ordinary_required_degree_from_reference_difference Target Sample Reference Bad Inner edit diff forbidden hEdit hDiff hBad,?_⟩
  have hLost:=lost_graph_degree_le_symmetric_edit Target Sample edit hEdit
  intro v
  have hrest:spanningRestriction (Sample\Reference) Inner≤Sample\Reference:=by
    intro x y h
    exact ((spanningRestriction_adj (Sample\Reference) Inner x y).mp h).1
  have hdrest:=SimpleGraph.degree_le_of_le hrest (v:=v)
  have hrest':((spanningRestriction (Sample\Reference) Inner).degree v:ℝ)≤((Sample\Reference).degree v:ℝ):=by
    exact_mod_cast hdrest
  have h1:=graph_degree_sup_le (Sample\Target) Protect v
  have h2:=graph_degree_sup_le ((Sample\Target)⊔Protect) (spanningRestriction (Sample\Reference) Inner) v
  have h3:=graph_degree_sup_le (ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner) Bad v
  have h1':(((Sample\Target)⊔Protect).degree v:ℝ)≤((Sample\Target).degree v:ℝ)+(Protect.degree v:ℝ):=by
    have hh:((Sample\Target)⊔Protect).degree v≤(Sample\Target).degree v+Protect.degree v:=by
      convert h1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  have h2':((ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v:ℝ)≤
      (((Sample\Target)⊔Protect).degree v:ℝ)+(spanningRestriction (Sample\Reference) Inner).degree v:=by
    have hh':(ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v≤
        ((Sample\Target)⊔Protect).degree v+(spanningRestriction (Sample\Reference) Inner).degree v:=by
      convert h2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh'
  have h3':((ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree v:ℝ)≤
      (ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v+Bad.degree v:=by
    have hh:(ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree v≤
        (ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v+Bad.degree v:=by
      convert h3 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  linarith [hLost v,hDiff v,hProtect v,hBad v]
end Oberwolfach
