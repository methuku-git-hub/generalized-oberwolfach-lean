module

public import Oberwolfach.MarkedReservedUnionSequentialIdentity
public import Oberwolfach.MarkedSamplePhysicalDeletionLift

@[expose] public section
/-! Equal raw samples and spoke relations give the same typed wheel packing,
with its physical resources unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_equal_sample_wheels_rebase
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hσ:σ=τ) (hH:H=H'):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    ∀ M:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)),
    (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    ∃ N:Finset (MarkedWheel (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) m π (3*d) (H' false) (H' true)),
      (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources:=by
  cases hσ
  cases hH
  intro E K E' K' M hM
  exact ⟨M,hM,rfl⟩

/-- A packing formed in the combined-deletion host is the same packing in
the sequential first-deletion-then-reservation host. -/
theorem marked_reserved_union_packing_to_sequential
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)):
    let RC:=physicalEdgeGraph (markedReservedRimPairs C)
    let SC:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let D:=DR⊔RC
    let Q:=DS⊔SC
    let edgeInst:Fintype D.edgeSet:=@SimpleGraph.fintypeEdgeSet V D (Sym2.instFintype)
      (fun x y=>Classical.propDecidable (D.Adj x y))
    let σU:=rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V D edgeInst)
    let HU:=markedDeletePhysicalSpokes H Q
    let σ₁:=rawMarkedDeleteRims σ DR.edgeFinset
    let H₁:=markedDeletePhysicalSpokes H DS
    let σS:=rawMarkedDeleteRims σ₁ RC.edgeFinset
    let HS:=markedDeletePhysicalSpokes H₁ SC
    let EU:=MarkedSampleArc P π (3*d) (fun e=>σU (Sum.inl e)) false
    let KU:=MarkedSampleArc P π (3*d) (fun e=>σU (Sum.inl e)) true;
    ∀ M:Finset (MarkedWheel (fun e:EU=>e.val.1) (fun e=>e.val.2)
      (fun e:KU=>e.val.1) (fun e=>e.val.2) m π (3*d) (HU false) (HU true)),
    (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    ∃ N:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ₁ RC SC H₁),
      (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources:=by
  intro RC SC D Q edgeInst σU HU σ₁ H₁ σS HS EU KU M hM
  have heq:=marked_reserved_union_sequential_identity σ H C DR DS
  exact marked_equal_sample_wheels_rebase P π d m σU σS HU HS heq.1 heq.2 M hM
end Oberwolfach
