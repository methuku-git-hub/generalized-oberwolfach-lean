module

public import Oberwolfach.OrderedOrdinaryWheelResources
public import Oberwolfach.MarkedPotentialSpokeAtHub

@[expose] public section
/-! The counting universe is equivalent to the full marked-wheel universe;
this is only an index-set equivalence, not an identification of sampled states. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

def orderedOrdinary_to_markedCycle
    (C:{C:Fin (m+1)→V // PermutationSeparated π b C}):
    MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b:=by
  refine ⟨C.val,C.property,?_,?_⟩
  · intro i;exact ⟨(C.val i.castSucc,C.val i.succ),rfl,rfl⟩
  · exact ⟨(C.val (Fin.last m),C.val 0),rfl,rfl⟩

def orderedOrdinaryMarkedWheelEquiv:
    OrderedOrdinaryWheel (U:=U) π b (m+1) ≃
      MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b (fun (_:V) (_:U)=>True) (fun _ _=>True) where
  toFun W:=markedFullWheel (orderedOrdinary_to_markedCycle W.1) W.2
  invFun W:=(⟨W.1.val,W.1.property.1⟩,W.2.val)
  left_inv W:=by cases W; rfl
  right_inv W:=by
    obtain ⟨C,⟨u,hu⟩⟩:=W
    rfl
end Oberwolfach
