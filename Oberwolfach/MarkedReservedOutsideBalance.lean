module

public import Oberwolfach.MarkedOutsideBalance

@[expose] public section

/-! Actual local balances after reserving inner edges and removing a
physical wheel packing. The reserved graph is not assumed divisible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {HK H₀:V→U→Prop} {m b:ℕ} {π:Equiv.Perm V}

theorem marked_reserved_outside_balance
    (A KA:Finset (E⊕K)) (S KS:Finset (V×U)) (I:Finset V) (J:Finset U)
    (hA:∀ a∈KA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)
    (hS:∀ s∈KS,s.1∈I∧s.2∈J)
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (hH:∀ x u,¬(H₀ x u∧HK x u))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hMA:M.biUnion markedWheelArcs⊆A\KA) (hMS:M.biUnion markedWheelSpokePairs⊆S\KS):
    MarkedOutsideBalance tail head ktail khead HK
      (A\(KA∪M.biUnion markedWheelArcs)) (S\(KS∪M.biUnion markedWheelSpokePairs)) m I J:=by
  have h:=MarkedOutsideBalance.sdiff (A\KA) (M.biUnion markedWheelArcs)
    (S\KS) (M.biUnion markedWheelSpokePairs) I J hMA hMS
    (MarkedOutsideBalance.remove_inner A KA S KS I J hA hS (hdiv.outside A S I J))
    (marked_packing_finite_divisible hH M hM)
  have hAE:(A\KA)\M.biUnion markedWheelArcs=A\(KA∪M.biUnion markedWheelArcs):=by
    ext a;simp only [Finset.mem_sdiff,Finset.mem_union];tauto
  have hSE:(S\KS)\M.biUnion markedWheelSpokePairs=S\(KS∪M.biUnion markedWheelSpokePairs):=by
    ext s;simp only [Finset.mem_sdiff,Finset.mem_union];tauto
  rw [hAE,hSE] at h
  exact h

end Oberwolfach
