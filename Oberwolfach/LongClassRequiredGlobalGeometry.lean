module

public import Oberwolfach.LongClassInnerRequiredRepair
public import Oberwolfach.LongPreparationIneligibleGraph

@[expose] public section
/-! The repaired required graph is supported on the inner set together with
permutation-close edges. This bounds its degree independently of the
assignment budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem long_class_required_global_geometry
    (S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    ∀v,Kplus.degree v≤I.card+(6*d+2) :=by
  intro K Kplus v
  have hsub:Kplus.neighborFinset v⊆I∪(longPreparationIneligibleGraph S π d).neighborFinset v:=by
    intro w hw
    have hadj:Kplus.Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
    change (longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y) ⊔
      spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I).Adj v w at hadj
    rcases hadj with hk|hextra
    · change (spanningRestriction ((S\Used)\Sel) I ⊔
        longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)).Adj v w at hk
      rcases hk with hinner|hclose
      · exact Finset.mem_union_left _ ((spanningRestriction_adj _ _ _ _).mp hinner).2.2
      · apply Finset.mem_union_right
        apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
        exact ⟨hclose.1,Or.inl hclose.2.1⟩
    · exact Finset.mem_union_left _ ((spanningRestriction_adj _ _ _ _).mp hextra).2.2
  have hcard:=Finset.card_le_card hsub
  have hunion:=Finset.card_union_le I ((longPreparationIneligibleGraph S π d).neighborFinset v)
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hcard hunion
  have hclose:=long_preparation_ineligible_degree S π d v
  omega
end Oberwolfach
