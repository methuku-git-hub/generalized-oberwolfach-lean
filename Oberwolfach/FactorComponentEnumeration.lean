module

public import Oberwolfach.FactorComponentEdges

@[expose] public section
/-! Produce an ordered cycle from each genuine component of a two-factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_component_enumeration (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (c:F.ConnectedComponent):
    ∃ (v:V) (rest:List V),
      (v::rest).Nodup ∧ 3≤(v::rest).length ∧
      (∀ x,x∈v::rest ↔ x∈c.supp) ∧
      (∀ x,x∈v::rest→∀ y,
        F.Adj x y ↔ s(x,y)∈prescribedOrderedPathEdges ((v::rest)++[v])) := by
  have hrep:∃ v:V,F.connectedComponentMk v=c := by
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => exact ⟨v,rfl⟩
  obtain ⟨v,hv⟩:=hrep
  obtain ⟨p,hcycle,hnodup,hlen,hclosed,hvertices,hedges⟩:=two_factor_component_ordered_edges F hF v
  have hne:p.support.dropLast≠[] := by
    apply List.ne_nil_of_length_pos
    omega
  have hfirst:p.support.dropLast.head hne=v := by
    simp [List.head_dropLast]
  have hcons:v::p.support.dropLast.tail=p.support.dropLast := by
    simpa [hfirst] using (List.cons_head_tail hne)
  refine ⟨v,p.support.dropLast.tail,?_,?_,?_,?_⟩
  · simpa only [hcons] using hnodup
  · simpa only [hcons] using hlen
  · intro x
    simpa only [hcons,hv] using hvertices x
  · intro x hx y
    have hx' : x∈p.support.dropLast := by simpa only [hcons] using hx
    simpa only [hcons,hclosed] using hedges x hx' y
end Oberwolfach
