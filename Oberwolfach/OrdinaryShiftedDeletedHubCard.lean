module

public import Oberwolfach.OrdinaryShiftedCommonHubCard
public import Oberwolfach.OrdinaryShiftedRimDeletion

@[expose] public section
/-! A later rim deletion does not change the ordinary-spoke count at any
hub, so the original common-sample count tests remain valid. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_deleted_hub_card
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (g j:Bool) (F:Finset (Sym2 V)) (u:U):
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw F
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw') (rawMarkedPairSpokes π d raw' g j)
    let e:{v // v∈bernoulliVertexSet st}↪_:=Function.Embedding.subtype _;
    ((restrictedResourceSubset e (ordinaryCommonHubSpokeRoots u)).card:ℝ)=
      rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j false u Finset.univ :=by
  intro raw raw' st e
  have hh:=retained_common_ordinary_hub_card (ordinaryShiftedPairRims P π d raw') (rawMarkedPairSpokes π d raw' g j) u
  have hr:=raw_spoke_hub_count_eq_card π d (fun e=>σ (Sum.inr e)) g j false u
  rw [hr]
  have hsp:∀v,rawMarkedPairSpokes π d raw' g j false v u↔
      rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false v u:=by
    intro v
    exact rawMarkedDeleteRims_spokes π d raw F g j false v u
  have hset:(Finset.univ.filter (fun v=>rawMarkedPairSpokes π d raw' g j false v u))=
      Finset.univ.filter (fun v=>rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false v u):=by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hsp]
  rw [←hset]
  exact_mod_cast hh
end Oberwolfach
