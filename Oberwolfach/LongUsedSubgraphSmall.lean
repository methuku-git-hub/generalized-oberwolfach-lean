module

public import Oberwolfach.LongPackedSmallExactArcs

@[expose] public section
/-! When the old packing equals the used matching edges, the small graph
contains the actual used graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_used_subgraph_small
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U]
    (Used:SimpleGraph V) (Pack:Finset (Sym2 V)) (E:U→Finset (Sym2 V))
    (hPack:Pack=Used.edgeFinset):
    Used≤SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))⊔prescribedPhysicalUnion E:=by
  intro x y hxy
  change (SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))).Adj x y ∨ (prescribedPhysicalUnion E).Adj x y
  left
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  refine ⟨?_,hxy.ne⟩
  rw [hPack]
  exact SimpleGraph.mem_edgeFinset.mpr hxy
end Oberwolfach
