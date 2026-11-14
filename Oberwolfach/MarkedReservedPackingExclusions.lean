module

public import Oberwolfach.MarkedPackingExclusionsAcrossResources
public import Oberwolfach.MarkedReservedPackingToReducedHost
public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section
/-! Prescribed exclusions survive transfer of a packing to the host in which
reserved physical resources have been removed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_packing_transfer_preserves_exclusions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    ∀ A:Finset (E⊕K),∀ S:Finset (V×U),
    (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    Disjoint C (M.biUnion markedWheelPhysicalResources)→
    Disjoint A (M.biUnion markedWheelArcs)→
    Disjoint S (M.biUnion markedWheelSpokePairs)→
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
    let A':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈A);
    ∃ M':Finset (MarkedWheel t' h' kt' kh' m π (3*d) (H' false) (H' true)),
      (∀ W∈M',∀ Z∈M',W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∧
      Disjoint A' (M'.biUnion markedWheelArcs) ∧ Disjoint S (M'.biUnion markedWheelSpokePairs):=by
  intro E K tail head ktail khead M A S hM hC hA hS DR DS σ' H' E' K' t' h' kt' kh' emb A'
  obtain ⟨M',hM',hres⟩:=marked_disjoint_packing_transfers_to_reserved_deletion P π d m σ H C M hM hC
  have hEnds:=markedSampleDeletedArcsEmbedding_endpoints_type P π d σ DR.edgeFinset
  have hx:=marked_packing_exclusions_transfer_on_resources
    (markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))) emb
    (fun a=>(hEnds a).1) (fun a=>(hEnds a).2.1) (fun a=>(hEnds a).2.2)
    M M' A A' S (fun a ha=>(Finset.mem_filter.mp ha).2) hres hA hS
  exact ⟨M',hM',hres,hx.1,hx.2⟩
end Oberwolfach
