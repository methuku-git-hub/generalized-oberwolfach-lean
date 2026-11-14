module

public import Oberwolfach.LongPreparationPhysicalContainment
public import Oberwolfach.PrescribedFamilyPhysicalDegree

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U]

theorem long_inner_selected_edges_avoid_completed_packing
    (S Sel Used Kbad:SimpleGraph V) (I:Finset V) (Pack:Finset (Sym2 V))
    (E:U→Finset (Sym2 V))
    (hClass:∀x∈I,∀y∈I,Sel.Adj x y→S.Adj x y)
    (hUsed:∀x y,Sel.Adj x y→¬Used.Adj x y)
    (hKbad:∀x∈I,∀y∈I,Sel.Adj x y→¬Kbad.Adj x y)
    (hPack:∀x y,Sel.Adj x y→s(x,y)∉Pack)
    (hE:∀u,Disjoint (E u) ((spanningRestriction (S\Used) I\Kbad).edgeFinset)):
    ∀x∈I,∀y∈I,Sel.Adj x y→
      ¬(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))⊔prescribedPhysicalUnion E).Adj x y:=by
  intro x hx y hy hSel hSmall
  rcases hSmall with hOld|hNew
  · have he:s(x,y)∈Pack:=(SimpleGraph.fromEdgeSet_adj _).mp hOld |>.1
    exact hPack x y hSel he
  · have hJ:(spanningRestriction (S\Used) I\Kbad).Adj x y:=by
      simp only [SimpleGraph.sdiff_adj,spanningRestriction_adj]
      exact ⟨⟨⟨hClass x hx y hy hSel,hUsed x y hSel⟩,hx,hy⟩,hKbad x hx y hy hSel⟩
    have he:s(x,y)∈(spanningRestriction (S\Used) I\Kbad).edgeFinset:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hJ
    have hnew:s(x,y)∈Finset.univ.biUnion E:=(SimpleGraph.fromEdgeSet_adj _).mp hNew |>.1
    obtain ⟨u,_,hu⟩:=Finset.mem_biUnion.mp hnew
    exact Finset.disjoint_left.mp (hE u) hu he
end Oberwolfach
