module

public import Oberwolfach.MarkedReferenceStateStepDecomposition

@[expose] public section
/-! A packing using only undeleted arcs and spokes has physical resources
contained in the current reference remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_packing_resources_subset_remaining
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (D:MarkedReferenceDeletion P π d σ):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ M:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)),
    M.biUnion markedWheelArcs⊆Finset.univ\D.arcs→
    M.biUnion markedWheelSpokePairs⊆S\D.spokes→
    M.biUnion markedWheelPhysicalResources⊆D.remaining H:=by
  intro E K S M hA hS
  rw [←markedPackingResources_eq_finite,D.remaining_eq]
  exact markedFiniteResources_mono hA hS
end Oberwolfach
