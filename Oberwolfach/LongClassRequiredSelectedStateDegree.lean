module

public import Oberwolfach.LongClassRequiredOutsideDegree
public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.MatchingExactPackingRepairVanishes

@[expose] public section
/-! After the full packing is fixed, required edges in a selected physical
state are permutation-close. Dense required inner edges therefore do not
contribute to the selected-state loss except through the spacing bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_class_required_selected_state_degree
    (P S Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P) (hPack:Pack=Used.edgeFinset):
    let Sel:=longSelectedPhysicalGraph P π d ω
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    ∀v,(Kplus⊓longPhysicalStateGraph P ω {1}).degree v≤6*d+2 :=by
  intro Sel K Kplus v
  have heq:Kplus=K:=matching_exact_class_packing_repair_vanishes S Used K I Pack hPack
  have hsub:(Kplus⊓longPhysicalStateGraph P ω {1}).neighborFinset v⊆
      (longPreparationIneligibleGraph P π d).neighborFinset v:=by
    intro w hw
    have hadj:Kplus.Adj v w ∧ (longPhysicalStateGraph P ω {1}).Adj v w:=
      (SimpleGraph.mem_neighborFinset _ _ _).mp hw
    by_contra hnot
    have hfar:¬(longPreparationIneligibleGraph P π d).Adj v w:=by
      intro h;exact hnot ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)
    have hstate:(ω (Sum.inl s(v,w))).1=1:=by
      have hh:=hadj.2.2
      simpa only [Finset.mem_singleton] using hh
    have hsel:Sel.Adj v w:=selected_state_outside_ineligible_is_selected P π d ω v w hadj.2.1 hfar (Or.inr hstate)
    have hk:K.Adj v w:=by rw [←heq];exact hadj.1
    change (spanningRestriction ((S\Used)\Sel) I ⊔
      longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)).Adj v w at hk
    rcases hk with hi|hc
    · exact ((spanningRestriction_adj _ _ _ _).mp hi).1.2 hsel
    · exact hfar ⟨hSP hc.1,Or.inl hc.2.1⟩
  have hc:=Finset.card_le_card hsub
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
  exact hc.trans (long_preparation_ineligible_degree P π d v)
end Oberwolfach
