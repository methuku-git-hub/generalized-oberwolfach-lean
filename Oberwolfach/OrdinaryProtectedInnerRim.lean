module

public import Oberwolfach.OrdinaryProtectedRequiredDegree

@[expose] public section
/-! Protect the whole inner reference rim as well as the fixed reservoir;
    this costs at most one additional inner-set size at each vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryProtectedInnerRim (Reference Reservoir:SimpleGraph V) (Inner:Finset V):SimpleGraph V :=
  Reservoir⊔spanningRestriction Reference Inner

theorem ordinary_protected_inner_rim_properties
    (Reference Reservoir:SimpleGraph V) (Inner:Finset V) (a:ℝ)
    (hsub:Reservoir≤Reference) (hdeg:∀v,(Reservoir.degree v:ℝ)≤a):
    Reservoir≤ordinaryProtectedInnerRim Reference Reservoir Inner ∧
    spanningRestriction Reference Inner≤ordinaryProtectedInnerRim Reference Reservoir Inner ∧
    ordinaryProtectedInnerRim Reference Reservoir Inner≤Reference ∧
    (∀v,((ordinaryProtectedInnerRim Reference Reservoir Inner).degree v:ℝ)≤a+Inner.card):=by
  refine ⟨le_sup_left,le_sup_right,?_,?_⟩
  · apply sup_le hsub
    intro v w h
    exact ((spanningRestriction_adj Reference Inner v w).mp h).1
  · intro v
    have hh:=graph_sup_degree_le Reservoir (spanningRestriction Reference Inner) v
    have hc:((ordinaryProtectedInnerRim Reference Reservoir Inner).degree v:ℝ)≤
        (Reservoir.degree v:ℝ)+(spanningRestriction Reference Inner).degree v:=by
      simp only [ordinaryProtectedInnerRim,←SimpleGraph.ncard_neighborSet] at hh ⊢
      exact_mod_cast hh
    have hi:((spanningRestriction Reference Inner).degree v:ℝ)≤Inner.card:=by
      exact_mod_cast ordinary_spanning_restriction_degree_card Reference Inner v
    linarith [hdeg v]
end Oberwolfach
