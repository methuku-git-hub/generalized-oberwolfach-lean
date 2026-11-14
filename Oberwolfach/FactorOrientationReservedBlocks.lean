module

public import Oberwolfach.FactorCycleOrientation
public import Oberwolfach.ExtendComponentCycleChoices
public import Oberwolfach.LongReservedSigmaBlocks

@[expose] public section
/-! The global factor orientation agrees with each original reserved cyclic
block because the selected component orders were preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_cycle_orientation_reserved_block_step
    {X I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent)
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (c d:ℕ) (q:LongReservedBlockIndex G components c d) (t:ℕ) (ht:t≤d)
    (j:Fin (c*t+4)):
    let E:=extendComponentCycleChoices G hG components e
    let σ:=factorCycleOrientation G E
    let block:=longReservedSigmaBlock G components c d e q t ht
    σ (block ⟨j.val,by omega⟩)=block ⟨j.val+1,by omega⟩:=by
  let E:=extendComponentCycleChoices G hG components e
  let σ:=factorCycleOrientation G E
  let C:=components q.1
  let fit:=long_reserved_sigma_block_fit G components c d q
  let block:=longReservedComponentBlock G C (e q.1) c d t q.2.val ht fit
  have hE:E C=e q.1:=extend_component_cycle_choices_selected G hG components e q.1
  have hσ:=factor_cycle_orientation_on_component G E C (block ⟨j.val,by omega⟩)
  change σ ((block ⟨j.val,by omega⟩).val)=(block ⟨j.val+1,by omega⟩).val
  rw [hσ,hE]
  apply congrArg Subtype.val
  dsimp [block,longReservedComponentBlock]
  simp only [RelIso.symm_apply_apply]
  apply congrArg (e q.1)
  apply Fin.ext
  rw [finRotate_apply]
  simp only [Fin.val_add]
  have hcard:Fintype.card C=Fintype.card (components q.1):=rfl
  have hthree:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1
  letI:NeZero (Fintype.card C):=⟨by omega⟩
  have hOne:((1:Fin (Fintype.card C)):ℕ)=1:=by
    rw [Fin.val_one',Nat.mod_eq_of_lt (by omega)]
  rw [hOne]
  have hprod:c*t≤c*d:=Nat.mul_le_mul_left c ht
  simp only [Nat.mul_add,Nat.mul_one] at fit
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
end Oberwolfach
