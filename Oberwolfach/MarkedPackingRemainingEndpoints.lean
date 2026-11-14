module

public import Oberwolfach.MarkedDeletedEndpointEmbeddings
public import Oberwolfach.MarkedFiniteDeletionDegrees
public import Oberwolfach.MarkedBoundaryRemainder

@[expose] public section

/-! The endpoint lists after an actual wheel packing enumerate exactly
its surviving original typed arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_packing_arc_coordinate_iff
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true))) (a:E⊕K),
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∈(markedPackingRimGraph M).edgeFinset↔
        Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources:=by
  intro E K tail head ktail khead M a
  rw [←markedSampleArcSetGraph_packing P π d m σ H M,markedSampleArcSetGraph_coordinate]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨W,hW,ha⟩
    exact ⟨W,hW,(markedWheel_arc_resource_iff (markedSampleArc_physical_injective P π (3*d) _) W a).mpr ha⟩
  · rintro ⟨W,hW,ha⟩
    exact ⟨W,hW,(markedWheel_arc_resource_iff (markedSampleArc_physical_injective P π (3*d) _) W a).mp ha⟩

theorem marked_deleted_endpoint_avoids_packing
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (X:Finset V) (incoming:Bool) (x:V):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (z:(markedEndpointLabels P π d X (false,incoming,x) (rawMarkedDeleteRims σ (markedPackingRimGraph M).edgeFinset))⊕
        (markedEndpointLabels P π d X (true,incoming,x) (rawMarkedDeleteRims σ (markedPackingRimGraph M).edgeFinset))),
    Sum.inl (markedPhysicalEdge tail head ktail khead π
      (markedDeletedEndpointArcEmbedding P π d X incoming x σ (markedPackingRimGraph M).edgeFinset z))∉
        M.biUnion markedWheelPhysicalResources:=by
  intro E K tail head ktail khead M z hz
  exact marked_deleted_endpoint_embedding_survives P π d X incoming x σ _ z
    ((marked_packing_arc_coordinate_iff P π d m σ H M _).mpr hz)

theorem marked_deleted_endpoint_exhausts_packing
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (X:Finset V) (incoming:Bool) (x:V) (hx:x∉X):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true))),
      (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
        Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)→
    ∀ a:E⊕K,(if incoming then Sum.elim head khead a else Sum.elim tail ktail a)=x→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉M.biUnion markedWheelPhysicalResources→
      ∃ z,markedDeletedEndpointArcEmbedding P π d X incoming x σ (markedPackingRimGraph M).edgeFinset z=a:=by
  intro E K tail head ktail khead M hcover a hroot hnot
  apply marked_deleted_endpoint_embedding_exhaustive P π d X incoming x σ _ a
    (fun he=>hnot ((marked_packing_arc_coordinate_iff P π d m σ H M a).mp he)) hroot
  by_contra hother
  cases incoming
  · simp only [Bool.false_eq_true,ite_false] at hroot hother
    exact hnot (hcover a (hroot ▸ hx) hother)
  · simp only [ite_true] at hroot hother
    exact hnot (hcover a hother (hroot ▸ hx))

end Oberwolfach
