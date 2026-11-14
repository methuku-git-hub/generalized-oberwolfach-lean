module

public import Oberwolfach.MarkedReservedFirstDeletionProtection
public import Oberwolfach.MarkedReservedDeepPackingLift

@[expose] public section
/-! A deep packing selected after the first deletion and after reserving the
absorber lifts to the first-deleted host; the two actual deletions preserve
the absorber's original typed resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_two_stage_lift_and_protection
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hb:1≤3*d)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true))),
    (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈S,z.1∈I∧z.2∈J)→Disjoint C (M.biUnion markedWheelPhysicalResources)→
    let DR₁:=markedSampleArcSetGraph P π d σ (A∪M.biUnion markedWheelArcs)
    let DS₁:=markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)
    let σ₁:=rawMarkedDeleteRims σ DR₁.edgeFinset
    let H₁:=markedDeletePhysicalSpokes H DS₁
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) false
    let K₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) true
    let tail₁:=fun e:E₁=>e.val.1
    let head₁:=fun e:E₁=>e.val.2
    let ktail₁:=fun e:K₁=>e.val.1
    let khead₁:=fun e:K₁=>e.val.2
    let RC:=physicalEdgeGraph (markedReservedRimPairs C)
    let SC:=markedFiniteSpokeGraph (markedReservedSpokePairs C);
    ∀ MD:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ₁ RC SC H₁),
    (∀ W∈MD,∀ Z∈MD,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    ∃ N:Finset (MarkedWheel tail₁ head₁ ktail₁ khead₁ m π (3*d) (H₁ false) (H₁ true)),
      (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      N.biUnion markedWheelPhysicalResources=MD.biUnion markedWheelPhysicalResources∧
      Disjoint C (N.biUnion markedWheelPhysicalResources)∧
      let DR₂:=markedPackingRimGraph N
      let DS₂:=markedFiniteSpokeGraph (N.biUnion markedWheelSpokePairs)
      let σ₂:=rawMarkedDeleteRims σ₁ DR₂.edgeFinset
      let H₂:=markedDeletePhysicalSpokes H₁ DS₂
      let E₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) false
      let K₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) true;
      (∀ e:E,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':E₂,e'.val=e.val) ∧
      (∀ e:K,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':K₂,e'.val=e.val) ∧
      (∀ b v u,Sum.inr (v,u)∈C→H b v u→H₂ b v u) :=by
  intro E K tail head ktail khead A S M hA hS hM DR₁ DS₁ σ₁ H₁ E₁ K₁ tail₁ head₁ ktail₁ khead₁ RC SC MD hMD
  obtain ⟨N,hN,hres,hdis⟩:=marked_reserved_deleted_packing_lift P π d m hm hb σ₁ H₁ C MD hMD
  refine ⟨N,hN,hres,hdis,?_⟩
  exact marked_two_stage_deletions_preserve_reserved_resources P π d m σ H C I J hI hC A S M hA hS hM N hdis
end Oberwolfach
