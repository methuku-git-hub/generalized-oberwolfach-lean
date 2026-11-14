module

public import Oberwolfach.LongClassInnerRequiredRepair

@[expose] public section
/-! In an inner-protected completion, a selected new edge outside the
required graph must cross the inner boundary. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem long_selected_extra_has_no_inner_edges
    (S Used K E Sel:SimpleGraph V) (I:Finset V) (hES:E≤S)
    (hAvoid:Disjoint E.edgeFinset ((spanningRestriction (S\Used) I)\K).edgeFinset)
    (hUsedSel:∀x y,Used.Adj x y→¬Sel.Adj x y):
    ∀x∈I,∀y∈I,¬(((E\K)⊓Sel).Adj x y) :=by
  intro x hx y hy h
  have he:E.Adj x y:=h.1.1
  have hk:¬K.Adj x y:=h.1.2
  have hu:¬Used.Adj x y:=by intro hu;exact hUsedSel x y hu h.2
  have hs:(spanningRestriction (S\Used) I\K).Adj x y:=by
    exact ⟨(spanningRestriction_adj _ _ _ _).mpr ⟨⟨hES he,hu⟩,hx,hy⟩,hk⟩
  have he':s(x,y)∈E.edgeFinset:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
  have hs':s(x,y)∈((spanningRestriction (S\Used) I)\K).edgeFinset:=by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hs
  exact (Finset.disjoint_left.mp hAvoid) he' hs' 
end Oberwolfach
