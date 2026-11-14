module

public import Oberwolfach.ApproximateAndFirstCoverProtectAbsorber

@[expose] public section
/-! Specialization to the manuscript's selected colour one and raw
approximate colour two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]

theorem long_class_matching_avoids_fixed_absorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U):
    let selected:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false t J false false
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let W:Type:={z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw true true))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z→
    ∀(C:Type) [Fintype C] [DecidableEq C] (Q:C→Finset W) (M:Finset C),
    Disjoint ((M.biUnion Q).image (fun w=>physicalResourceToFinite (φ w))) Reserve :=by
  intro selected H raw W φ habs C _ _ Q M
  exact raw_matching_avoids_fixed_terminal_absorber P π d m σ false true (by decide) t J false true (by decide) Reserve X Z habs C Q M
end Oberwolfach
