module

public import Oberwolfach.LongClassInnerRequiredRepair
public import Oberwolfach.LongPreparationIneligibleGraph

@[expose] public section
/-! Outside the protected inner set, the repaired required graph contains
only permutation-close edges. Its degree is independent of the global
assignment allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem long_class_required_outside_degree
    (P S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    ∀v,v∉I→Kplus.degree v≤6*d+2 :=by
  intro K Kplus v hv
  have hsub:Kplus.neighborFinset v⊆(longPreparationIneligibleGraph P π d).neighborFinset v:=by
    intro w hw
    have hadj:Kplus.Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
    change (longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y) ⊔
      spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I).Adj v w at hadj
    rcases hadj with hk|hextra
    · change (spanningRestriction ((S\Used)\Sel) I ⊔
        longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)).Adj v w at hk
      rcases hk with hinner|hclose
      · exact (hv ((spanningRestriction_adj _ _ _ _).mp hinner).2.1).elim
      · apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
        exact ⟨hSP hclose.1,Or.inl hclose.2.1⟩
    · exact (hv ((spanningRestriction_adj _ _ _ _).mp hextra).2.1).elim
  have hcard:=Finset.card_le_card hsub
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact hcard.trans (long_preparation_ineligible_degree P π d v)
end Oberwolfach
