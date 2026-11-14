module

public import Oberwolfach.MarkedActualSampleMatchingDisjoint

@[expose] public section
/-! Approximate matching resources avoid the entire retained reference sample,
including every corrected remainder on that sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem marked_actual_sample_remaining_avoids_matching
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (D₀:MarkedReferenceDeletion P π d (markedExpandedActualSelected π d z).1):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let R:Type:={x // x∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw true true))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    ∀ (C:Type) [Fintype C] [DecidableEq C] (Qc:C→Finset R) (M:Finset C),
      Disjoint ((M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ w))) (D₀.remaining H) := by
  intro H raw R φ C _ _ Qc M
  let Dfull:MarkedReferenceDeletion P π d (markedExpandedActualSelected π d z).1 :=
    ⟨Finset.univ,Finset.univ.filter (fun p:V×U=>H false p.1 p.2∨H true p.1 p.2)⟩
  have hd:MarkedDeletionAvoidsApproximateMatching P π d z Dfull := by
    apply marked_actual_sample_deletion_avoids_matching P π d z Dfull
    dsimp only [Dfull,H]
    exact Finset.Subset.rfl
  have hfull:=hd C Qc M
  have hsubset:D₀.remaining H⊆Dfull.removed:=by
    intro x hx
    dsimp only [MarkedReferenceDeletion.remaining] at hx
    have hxFull:=(Finset.mem_sdiff.mp hx).1
    simpa only [Dfull,MarkedReferenceDeletion.removed] using hxFull
  exact Finset.disjoint_of_subset_right hsubset hfull
end Oberwolfach
