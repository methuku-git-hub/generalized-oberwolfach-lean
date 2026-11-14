module

public import Oberwolfach.MarkedDeletedSampleOutsideBalance
public import Oberwolfach.MarkedFiniteDeletionDegrees
public import Oberwolfach.MarkedReservedOutsideBalance

@[expose] public section

/-! Deleting an actual wheel packing preserves the outside balances in
the resulting physical sample. An inner reservation can first be removed
without imposing global divisibility on that reservation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_packing_deletion_outside_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (hH:∀ x u,¬(H false x u∧H true x u))
    (X:Finset V) (Z:Finset U):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    MarkedOutsideBalance tail head ktail khead (H true) Finset.univ S m X Z→
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ W∈M,∀ Y∈M,W≠Y→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Y))→
    let σ':=rawMarkedDeleteRims σ (markedPackingRimGraph M).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs))
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    MarkedOutsideBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) m X Z:=by
  intro E₀ E₁ tail head ktail khead S h M hM
  have hMS:M.biUnion markedWheelSpokePairs⊆S:=by
    intro z hz
    obtain ⟨W,hW,hz⟩:=Finset.mem_biUnion.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,markedWheelPhysicalResources_spoke_present W z.1 z.2
      ((markedWheel_spoke_resource W z).mp hz)⟩
  have hh:=MarkedOutsideBalance.sdiff Finset.univ (M.biUnion markedWheelArcs)
    S (M.biUnion markedWheelSpokePairs) X Z (Finset.subset_univ _) hMS h
    (marked_packing_finite_divisible hH M hM)
  apply marked_deleted_sample_outside_balance P π d m σ H
    (markedPackingRimGraph M) (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)) X Z
  rw [←markedSampleArcSetGraph_packing P π d m σ H M,markedSampleArcSetGraph_remaining]
  have he:Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧
      ¬(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).Adj (Sum.inl z.1) (Sum.inr z.2))=
      S\M.biUnion markedWheelSpokePairs:=by
    ext z
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,markedFiniteSpokeGraph_adj]
  rw [he]
  exact hh

theorem marked_reserved_sample_outside_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (hH:∀ x u,¬(H false x u∧H true x u))
    (X:Finset V) (Z:Finset U):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    ∀ (KA:Finset (E₀⊕E₁)) (KS:Finset (V×U)),
    (∀ a∈KA,Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)→
    (∀ z∈KS,z.1∈X∧z.2∈Z)→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m→
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ W∈M,∀ Y∈M,W≠Y→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Y))→
    M.biUnion markedWheelArcs⊆Finset.univ\KA→M.biUnion markedWheelSpokePairs⊆S\KS→
    let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    MarkedOutsideBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) m X Z:=by
  intro E₀ E₁ tail head ktail khead S KA KS hKA hKS hdiv M hM hMA hMS
  have hh:=marked_reserved_outside_balance Finset.univ KA S KS X Z hKA hKS hdiv hH M hM hMA hMS
  apply marked_deleted_sample_outside_balance P π d m σ H
    (markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs))
    (markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)) X Z
  rw [markedSampleArcSetGraph_remaining]
  have he:Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧
      ¬(markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)).Adj (Sum.inl z.1) (Sum.inr z.2))=
      S\(KS∪M.biUnion markedWheelSpokePairs):=by
    ext z
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,markedFiniteSpokeGraph_adj]
  rw [he]
  exact hh

end Oberwolfach
