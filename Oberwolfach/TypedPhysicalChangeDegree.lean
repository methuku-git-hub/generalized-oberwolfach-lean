module

public import Oberwolfach.TypedPhysicalChangeContainment
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! Physical graph closeness and a sparse retyping graph give closeness of
each type-specific physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem typed_change_degree_from_physical_and_retyping
    {V:Type} [Fintype V] [DecidableEq V] (Ref Now RefType NowType Retype:SimpleGraph V)
    (hRef:RefType≤Ref) (hNow:NowType≤Now)
    (hAgree:∀x y,Ref.Adj x y→Now.Adj x y→¬Retype.Adj x y→(RefType.Adj x y↔NowType.Adj x y))
    (x:V) (η δ:ℝ)
    (hPhysical:((changed (Ref.neighborFinset x) (Now.neighborFinset x)).card:ℝ)≤η)
    (hRetype:(Retype.degree x:ℝ)≤δ):
    ((changed (RefType.neighborFinset x) (NowType.neighborFinset x)).card:ℝ)≤η+δ:=by
  have hsub:=typed_change_contained_in_physical_and_retyping Ref Now RefType NowType Retype hRef hNow hAgree
  have hle:((((RefType\NowType)⊔(NowType\RefType)).degree x):ℝ)≤
      (((((Ref\Now)⊔(Now\Ref))⊔Retype).degree x):ℝ):=by
    have hn:((RefType\NowType)⊔(NowType\RefType)).degree x≤(((Ref\Now)⊔(Now\Ref))⊔Retype).degree x:=by
      convert SimpleGraph.degree_le_of_le hsub using 1 <;> congr!
    exact_mod_cast hn
  have hsum:(((((Ref\Now)⊔(Now\Ref))⊔Retype).degree x):ℝ)≤
      ((((Ref\Now)⊔(Now\Ref)).degree x):ℝ)+Retype.degree x:=by
    have hn:(((Ref\Now)⊔(Now\Ref))⊔Retype).degree x≤((Ref\Now)⊔(Now\Ref)).degree x+Retype.degree x:=by
      convert graph_degree_sup_le ((Ref\Now)⊔(Now\Ref)) Retype x using 1 <;> congr!
    exact_mod_cast hn
  have hA:((((RefType\NowType)⊔(NowType\RefType)).degree x):ℝ)=
      ((changed (RefType.neighborFinset x) (NowType.neighborFinset x)).card:ℝ):=by
    exact_mod_cast graph_symmetric_difference_degree RefType NowType x
  have hB:((((Ref\Now)⊔(Now\Ref)).degree x):ℝ)=
      ((changed (Ref.neighborFinset x) (Now.neighborFinset x)).card:ℝ):=by
    exact_mod_cast graph_symmetric_difference_degree Ref Now x
  linarith
end Oberwolfach
