module

public import Oberwolfach.LongClassRequiredOutsideDegree

@[expose] public section
/-! Required edges leaving the first inner set have bounded degree even at
an inner vertex; the dense contribution is confined to edges inside it. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem long_class_required_crossing_degree
    (P S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    ∀v,((Kplus.neighborFinset v).filter (fun w=>w∉I)).card≤6*d+2 :=by
  intro K Kplus v
  have hsub:(Kplus.neighborFinset v).filter (fun w=>w∉I)⊆(longPreparationIneligibleGraph P π d).neighborFinset v:=by
    intro w hw
    have hmem:=Finset.mem_filter.mp hw
    have hadj:Kplus.Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hmem.1
    change (longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y) ⊔
      spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I).Adj v w at hadj
    rcases hadj with hk|hextra
    · change (spanningRestriction ((S\Used)\Sel) I ⊔
        longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)).Adj v w at hk
      rcases hk with hinner|hclose
      · exact (hmem.2 ((spanningRestriction_adj _ _ _ _).mp hinner).2.2).elim
      · apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
        exact ⟨hSP hclose.1,Or.inl hclose.2.1⟩
    · exact (hmem.2 ((spanningRestriction_adj _ _ _ _).mp hextra).2.2).elim
  have hcard:=Finset.card_le_card hsub
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact hcard.trans (long_preparation_ineligible_degree P π d v)
end Oberwolfach
