module

public import Oberwolfach.ActualSelectedPackingPhysicalSurjective
public import Oberwolfach.RawMarkedWheelInterval

@[expose] public section
/-! The marked wheel's sampled spoke supplies its interval address; the
actual selected runs therefore contain every packed marked wheel at the hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_raw_selected_physical_packing_wheels_surjective
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V]
    [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (π:Equiv.Perm V)
    (raw:RawMarkedOutcome V U Bool Bool) (root:K→V) (hub:U)
    (M:Finset (MarkedWheel tail head ktail khead m π b
      (rawMarkedPairSpokes π data.d raw true true false) (rawMarkedPairSpokes π data.d raw true true true)))
    (hpack:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hHub:∀Z∈M,Z.2.val=hub)
    (hT:∀i∈data.s₂,data.T i=packedPhysicalSpokePositions tail head ktail khead m b data.d π
      (rawMarkedPairSpokes π data.d raw true true false) (rawMarkedPairSpokes π data.d raw true true true) M hub (root i))
    (hrootcover:∀a,rawIntervalColouredStart π data.d (fun e=>raw (Sum.inr (hub,e))) a true→
      ∃i∈data.s₂,root i=a)
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b
      (rawMarkedPairSpokes π data.d raw true true false) (rawMarkedPairSpokes π data.d raw true true true))
    (hW:∀z,W z∈M ∧ (W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val)):
    ∀Z∈M,∃z,W z=Z:=by
  apply actual_selected_physical_packing_wheels_surjective data tail head ktail khead m b π _ _ root M hub hpack hT ?_ W hW
  intro Z hZ
  have hh:=hHub Z hZ
  obtain ⟨a,⟨ha,hx⟩,_⟩:=raw_marked_wheel_unique_interval π data.d m b raw true true Z
  rw [hh] at ha
  obtain ⟨i,hi,hri⟩:=hrootcover a ha
  obtain ⟨j,hj⟩:=(permutationWindow_mem_iff π 0 (data.d-1) a (Z.1.val 0)).mp hx
  refine ⟨hh,i,hi,j.val,?_,?_⟩
  · have hd:=data.hd
    have hj' := j.isLt
    omega
  · simpa only [pow_zero,Equiv.Perm.one_apply,hri] using hj.symm
end Oberwolfach
