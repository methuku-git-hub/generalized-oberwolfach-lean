module

public import Oberwolfach.MarkedExpandedActualSample
public import Oberwolfach.MarkedCorrectionMatchingSameSample

@[expose] public section
/-! The actual retained sample's reference deletion avoids all matching
resources in the approximate layer of the same expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

def MarkedDeletionAvoidsApproximateMatching
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (D₀:MarkedReferenceDeletion P π d (markedExpandedActualSelected π d z).1):Prop:=
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let R:Type:={x // x∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw true true))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    ∀ (C:Type) [Fintype C] [DecidableEq C] (Qc:C→Finset R) (M:Finset C),
      Disjoint ((M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ w))) D₀.removed

theorem marked_actual_sample_deletion_avoids_matching
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (D₀:MarkedReferenceDeletion P π d (markedExpandedActualSelected π d z).1):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false;
    D₀.spokes⊆Finset.univ.filter (fun x:V×U=>H false x.1 x.2∨H true x.1 x.2) →
    MarkedDeletionAvoidsApproximateMatching P π d z D₀ := by
  intro H hsub
  exact marked_reference_deletion_avoids_approximate_matching P π d z.1 z.2 D₀ hsub
end Oberwolfach
