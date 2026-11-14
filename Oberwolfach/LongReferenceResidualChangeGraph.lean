module

public import Oberwolfach.TypedPhysicalChangeContainment
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! The physical comparison, orientation deletion and retyping changes form
one bounded graph suitable for reference-stability lemmas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longReferenceResidualChangeGraph {V:Type} (Ref Now Del Retype:SimpleGraph V):SimpleGraph V:=
  (((Ref\Now)⊔(Now\Ref))⊔Del)⊔Retype

theorem long_reference_residual_change_graph_degree
    {V:Type} [Fintype V] [DecidableEq V] (Ref Now Del Retype:SimpleGraph V)
    (η δ χ:ℝ)
    (hPhysical:∀x,((changed (Ref.neighborFinset x) (Now.neighborFinset x)).card:ℝ)≤η)
    (hDel:∀x,(Del.degree x:ℝ)≤δ) (hRetype:∀x,(Retype.degree x:ℝ)≤χ):
    ∀x,((longReferenceResidualChangeGraph Ref Now Del Retype).degree x:ℝ)≤η+δ+χ:=by
  intro x
  let Diff:SimpleGraph V:=(Ref\Now)⊔(Now\Ref)
  have hdiff:(Diff.degree x:ℝ)=((changed (Ref.neighborFinset x) (Now.neighborFinset x)).card:ℝ):=by
    exact_mod_cast graph_symmetric_difference_degree Ref Now x
  have h1:(((Diff⊔Del)⊔Retype).degree x:ℝ)≤((Diff⊔Del).degree x:ℝ)+Retype.degree x:=by
    have hn:((Diff⊔Del)⊔Retype).degree x≤(Diff⊔Del).degree x+Retype.degree x:=by
      convert graph_degree_sup_le (Diff⊔Del) Retype x using 1 <;> congr!
    exact_mod_cast hn
  have h2:((Diff⊔Del).degree x:ℝ)≤(Diff.degree x:ℝ)+Del.degree x:=by
    have hn:(Diff⊔Del).degree x≤Diff.degree x+Del.degree x:=by
      convert graph_degree_sup_le Diff Del x using 1 <;> congr!
    exact_mod_cast hn
  change (((Diff⊔Del)⊔Retype).degree x:ℝ)≤η+δ+χ
  linarith [hPhysical x,hDel x,hRetype x]
end Oberwolfach
