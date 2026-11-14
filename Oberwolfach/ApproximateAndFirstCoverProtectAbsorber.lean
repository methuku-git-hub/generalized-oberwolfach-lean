module

public import Oberwolfach.FixedAbsorberSelectedSupport
public import Oberwolfach.MarkedReservedDeepPackingLift

@[expose] public section
/-! The raw approximate matching and any first cover packing constructed in
the reserve-deleted selected host both avoid the same fixed absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem approximate_and_first_cover_protect_fixed_absorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hd:1≤3*d)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g₀ g₂:Γ) (hg:g₂≠g₀) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g₀) t)
    (j₁ j₂:Color) (hj:j₂≠j₁) (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U):
    let selected:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g₀ t J g₀ j₁
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let W:Type:={z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g₂ j₂))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g₂ j₂
    let DR:=physicalEdgeGraph (markedReservedRimPairs Reserve)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs Reserve)
    let E:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>selected (Sum.inl e)) true
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z→
    ∀(C:Type) [Fintype C] [DecidableEq C] (Q:C→Finset W) (M:Finset C),
    ∀N:Finset (MarkedPhysicalDeletedSampleWheel P π d m selected DR DS H),
    (∀W∈N,∀Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    Disjoint ((M.biUnion Q).image (fun w=>physicalResourceToFinite (φ w))) Reserve ∧
    ∃N':Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)),
      (∀W∈N',∀Z∈N',W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      N'.biUnion markedWheelPhysicalResources=N.biUnion markedWheelPhysicalResources ∧
      Disjoint Reserve (N'.biUnion markedWheelPhysicalResources) :=by
  intro selected H raw W φ DR DS E K habs C _ _ Q M N hN
  constructor
  · exact raw_matching_avoids_fixed_terminal_absorber P π d m σ g₀ g₂ hg t J j₁ j₂ hj Reserve X Z habs C Q M
  · exact marked_reserved_deleted_packing_lift P π d m hm hd selected H Reserve N hN
end Oberwolfach
