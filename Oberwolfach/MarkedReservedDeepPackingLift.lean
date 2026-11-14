module

public import Oberwolfach.MarkedReservedDeletedSampleAvoidance

@[expose] public section
/-! A packing chosen after deleting the reserved graphs lifts to the previous
host with identical physical resources and remains disjoint from the reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_deleted_packing_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hb:1≤3*d)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (C:Finset (Finset V⊕(V×U))):
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ M:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H),
    (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    ∃ N:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)),
    (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
    N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∧
    Disjoint C (N.biUnion markedWheelPhysicalResources):=by
  intro DR DS E K M hM
  let N:=M.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H)
  have hlift:=markedPhysicalDeletedSamplePacking_lift P π d m σ DR DS H M hM
  have hdis:=marked_deleted_sample_packing_avoids_reserved_resources P π d m hm hb σ H C DR DS le_rfl le_rfl M
  refine ⟨N,hlift.2.1,hlift.1,?_⟩
  rw [hlift.1]
  exact hdis
end Oberwolfach
