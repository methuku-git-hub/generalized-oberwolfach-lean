module

public import Oberwolfach.LongClassRequiredSelectedStateDegree

@[expose] public section
/-! The marked-state portion of a completed packing is controlled by its
extra edges outside the required graph plus a fixed spacing error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_selected_loss_outside_required_bound
    (P S Used Loss:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P) (hPack:Pack=Used.edgeFinset):
    let Sel:=longSelectedPhysicalGraph P π d ω
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    ∀v,(Loss⊓longPhysicalStateGraph P ω {1}).degree v≤
      (Loss\Kplus).degree v+(6*d+2) :=by
  intro Sel K Kplus v
  have hsub:(Loss⊓longPhysicalStateGraph P ω {1}).neighborFinset v⊆
      (Loss\Kplus).neighborFinset v∪(Kplus⊓longPhysicalStateGraph P ω {1}).neighborFinset v:=by
    intro w hw
    have h:(Loss⊓longPhysicalStateGraph P ω {1}).Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
    by_cases hk:Kplus.Adj v w
    · apply Finset.mem_union_right
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ⟨hk,h.2⟩
    · apply Finset.mem_union_left
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ⟨h.1,hk⟩
  have hcard:=Finset.card_le_card hsub
  have hunion:=Finset.card_union_le ((Loss\Kplus).neighborFinset v)
    ((Kplus⊓longPhysicalStateGraph P ω {1}).neighborFinset v)
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hcard hunion
  have hK:=long_class_required_selected_state_degree P S Used π d I ω Req Pack hSP hPack v
  have hK':(Kplus⊓longPhysicalStateGraph P ω {1}).degree v≤6*d+2:=by
    convert hK using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  omega
end Oberwolfach
