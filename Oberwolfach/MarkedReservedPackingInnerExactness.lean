module

public import Oberwolfach.MarkedReservedPackingExclusions
public import Oberwolfach.MarkedReservedInnerResourceSetLift

@[expose] public section
/-! The prescribed inner-resource identity and exclusions survive together
when a packing is transferred to the absorber-deleted host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_packing_transfer_preserves_inner_exactness
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (A DA:Finset (E⊕K)) (S DS₀:Finset (V×U)),
    (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    Disjoint C (M.biUnion markedWheelPhysicalResources)→
    Disjoint A (M.biUnion markedWheelArcs)→Disjoint S (M.biUnion markedWheelSpokePairs)→
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)→
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
    let A':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈A)
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA);
    ∃ M':Finset (MarkedWheel t' h' kt' kh' m π (3*d) (H' false) (H' true)),
      (∀ X∈M',∀ Y∈M',X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))∧
      M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∧
      Disjoint A' (M'.biUnion markedWheelArcs)∧Disjoint S (M'.biUnion markedWheelSpokePairs)∧
      (M'.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
        (markedFiniteResources t' h' kt' kh' π DA' DS₀).filter (markedStarResource T W):=by
  intro E K tail head ktail khead M A DA S DS₀ hM hdis hA hS hDA hexact DR DS σ' H' E' K' t' h' kt' kh' emb A' DA'
  obtain ⟨M',hM',hres,hA',hS'⟩:=marked_reserved_packing_transfer_preserves_exclusions P π d m σ H C M A S hM hdis hA hS
  have hlift:=marked_reserved_inner_resources_lift P π d σ C I J hI hC DA DS₀ hDA
  exact ⟨M',hM',hres,hA',hS',by rw [hres,hlift.2.2];exact hexact⟩
end Oberwolfach
