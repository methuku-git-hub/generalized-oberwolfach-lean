module

public import Oberwolfach.InnerReservedGraph

@[expose] public section
/-! The repair term vanishes when the old packing is the full matching edge set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem matching_exact_packing_repair_vanishes
    {V:Type} [Fintype V] [DecidableEq V]
    (Used K:SimpleGraph V) (I:Finset V) (Pack:Finset (Sym2 V))
    (hPack:Pack=Used.edgeFinset):
    K⊔spanningRestriction (Used\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I=K:=by
  ext x y
  change K.Adj x y ∨ (spanningRestriction (Used\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I).Adj x y ↔ K.Adj x y
  constructor
  · intro h
    rcases h with hk|hr
    · exact hk
    · have hh:=(spanningRestriction_adj _ _ _ _).mp hr
      have hu:Used.Adj x y:=hh.1.1
      have hp:s(x,y)∈Pack:=by rw [hPack]; exact SimpleGraph.mem_edgeFinset.mpr hu
      have hfrom:(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))).Adj x y:=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨hp,Used.ne_of_adj hu⟩
      exact False.elim (hh.1.2 hfrom)
  · exact Or.inl
theorem matching_exact_class_packing_repair_vanishes
    {V:Type} [Fintype V] [DecidableEq V]
    (S Used K:SimpleGraph V) (I:Finset V) (Pack:Finset (Sym2 V))
    (hPack:Pack=Used.edgeFinset):
    K⊔spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I=K:=by
  ext x y
  change K.Adj x y ∨ (spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I).Adj x y ↔ K.Adj x y
  constructor
  · intro h
    rcases h with hk|hr
    · exact hk
    · have hh:=(spanningRestriction_adj _ _ _ _).mp hr
      have hu:Used.Adj x y:=hh.1.1.2
      have hp:s(x,y)∈Pack:=by rw [hPack]; exact SimpleGraph.mem_edgeFinset.mpr hu
      have hfrom:(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))).Adj x y:=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨hp,Used.ne_of_adj hu⟩
      exact False.elim (hh.1.2 hfrom)
  · exact Or.inl
end Oberwolfach
