module

public import Oberwolfach.MarkedReservedDeletedSampleAvoidance
public import Oberwolfach.ResourceDecompositions

@[expose] public section
/-! A packing in the original host and a decomposition in a host obtained
by deleting its physical resource graphs combine into a decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_packing_union_with_deleted_host_decomposition
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hd:1≤3*d)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))→
    physicalEdgeGraph (markedReservedRimPairs (M.biUnion markedWheelPhysicalResources))≤DR→
    markedFiniteSpokeGraph (markedReservedSpokePairs (M.biUnion markedWheelPhysicalResources))≤DS→
    ∀ S:Finset (Finset V⊕(V×U)),
    HasResourceDecomposition
      (fun W:MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H=>markedWheelPhysicalResources W) S→
    HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
      (M.biUnion markedWheelPhysicalResources∪S):=by
  intro E K tail head ktail khead M hM hR hS S hdec
  obtain ⟨N,hN,hNres⟩:=hdec
  have hdis:=marked_deleted_sample_packing_avoids_reserved_resources P π d m hm hd σ H
    (M.biUnion markedWheelPhysicalResources) DR DS hR hS N
  rw [hNres] at hdis
  let N':=N.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H)
  have hlift:=markedPhysicalDeletedSamplePacking_lift P π d m σ DR DS H N hN
  have hNdec:HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) S:=
    ⟨N',hlift.2.1,hlift.1.trans hNres⟩
  exact resource_decomposition_union _ _ _ ⟨M,hM,rfl⟩ hNdec hdis
end Oberwolfach
