module

public import Oberwolfach.RetainedCommonHubCard
public import Oberwolfach.RawVariableSpokeHubCounts
public import Oberwolfach.OrdinaryShiftedMarkedResourceState
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! The active ordinary-spoke roots at a hub are exactly the raw ordinary
spokes on the same expanded sample, independently of the rim host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_common_hub_card
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e) (g j:Bool) (u:U):
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{v // v∈bernoulliVertexSet st}↪_:=Function.Embedding.subtype _;
    ((restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:ℝ)=
      rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j false u Finset.univ :=by
  intro raw st e
  have hh:=retained_common_ordinary_hub_card (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j) u
  have hr:=raw_spoke_hub_count_eq_card π d (fun e=>σ (Sum.inr e)) g j false u
  rw [hr]
  exact_mod_cast hh
end Oberwolfach
