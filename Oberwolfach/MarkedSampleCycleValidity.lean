module

public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.SuccessorSequencePositionBounds

@[expose] public section

/-! An actual sampled marked cycle is a valid parent successor sequence.
The conversion retains the last edge's permutation and every ordered label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem marked_sample_cycle_valid (P:SimpleGraph V) (π:Equiv.Perm V) (b m:ℕ)
    (σ:Sym2 V→Option (Bool×Bool))
    (C:MarkedCycleTuple (fun e:MarkedSampleArc P π b σ false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π b σ true=>e.val.1) (fun e=>e.val.2) m π b):
    SuccessorSequenceValid P π C.val:=by
  intro i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · obtain ⟨e,he⟩:=C.property.2.2
    have hh:=((markedPhysicalRim_eq_one_iff P π b σ true e.val.1 e.val.2).mp e.property).2.1
    simpa only [ite_true,he.1,he.2,Fin.val_last,cycleNext_last] using hh
  · obtain ⟨e,he⟩:=C.property.2.1 j
    have hh:=((markedPhysicalRim_eq_one_iff P π b σ false e.val.1 e.val.2).mp e.property).2.1
    simpa only [Bool.false_eq_true,ite_false,he.1,he.2,Fin.val_castSucc,
      show j.val+1≠m+1 by omega,cycleNext_castSucc] using hh

end Oberwolfach
