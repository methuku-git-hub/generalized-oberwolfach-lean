module

public import Oberwolfach.MarkedWheelVertexEmbedding
public import Oberwolfach.MarkedSamplePhysicalDeletionLift
public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section

/-! Lift a packing on the actual active induced pair after physical
rim and spoke deletions. This uses the restricted original outcome; no
new outcome or alternative direction assignment is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A B Gamma Color:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B]
  [Fintype Gamma] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

abbrev MarkedActiveDeletedWheel
    (f:A↪oV) (g:B↪U) (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (d m:ℕ) (σ:RawMarkedOutcome V U Gamma Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)):=
  let σ':=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
  MarkedWheel
    (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
    (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
    m ρ (3*d) (fun x u=>markedDeletePhysicalSpokes H DS false (f x) (g u))
      (fun x u=>markedDeletePhysicalSpokes H DS true (f x) (g u))

theorem marked_active_deleted_packing_lift
    (f:A↪oV) (g:B↪U) (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x))
    (d m:ℕ) (σ:RawMarkedOutcome V U Gamma Color) (H:Bool→V→U→Prop)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (M:Finset (MarkedActiveDeletedWheel f g P π ρ d m σ H DR DS))
    (hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)):
    ∃ N:Finset (MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true)),
    N.biUnion markedWheelPhysicalResources=
      (M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f.toEmbedding g)∧
    (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
    Disjoint (markedPackingRimGraph N) DR∧
    (∀ x u,markedPackingSpokes N x u→¬DS.Adj (Sum.inl x) (Sum.inr u)):=by
  let σ':=rawMarkedDeleteRims σ DR.edgeFinset
  let σA:=rawMarkedRestrictPair f g σ'
  let e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false→
      MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false:=fun e=>
    ⟨(f e.val.1,f e.val.2),(markedPhysicalRim_orderEmbedding f π ρ hf P (3*d)
      (fun e=>σ' (Sum.inl e)) false e.val.1 e.val.2).mp e.property⟩
  let k:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true→
      MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true:=fun e=>
    ⟨(f e.val.1,f e.val.2),(markedPhysicalRim_orderEmbedding f π ρ hf P (3*d)
      (fun e=>σ' (Sum.inl e)) true e.val.1 e.val.2).mp e.property⟩
  let F:MarkedActiveDeletedWheel f g P π ρ d m σ H DR DS↪
      MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H:=markedWheelVertexEmbedding f.toEmbedding g hf e k
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (fun _ _ h=>h) (fun _ _ h=>h)
  have hMF:∀ W∈M.image F,∀ Z∈M.image F,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z):=
    markedPackingVertexEmbedding_matching f.toEmbedding g hf e k
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h) M hM
  have hres:(M.image F).biUnion markedWheelPhysicalResources=
      (M.biUnion markedWheelPhysicalResources).image (markedResourceEmbedding f.toEmbedding g):=
    markedPackingVertexEmbedding_resources f.toEmbedding g hf e k
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h) M
  have hLift:=markedPhysicalDeletedSamplePacking_lift P π d m σ DR DS H (M.image F) hMF
  refine ⟨(M.image F).image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H),
    hLift.1.trans hres,hLift.2⟩

end Oberwolfach
