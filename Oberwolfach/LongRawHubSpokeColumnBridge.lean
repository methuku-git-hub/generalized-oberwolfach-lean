module

public import Oberwolfach.LongRawHubContext
public import Oberwolfach.RawVariableSpokeHubCounts
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! The ordinary spoke-column event counts exactly the active ordinary
hub roots in the actual approximate raw state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance spokeBridgeFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_ordinary_hub_roots_eq_spoke_column
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (g j:Bool) (u:U):
    (((ordinaryCommonHubSpokeRoots u).filter (fun z=>
       longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) g j z=true)).card:ℝ)=
    rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j false u Finset.univ :=by
  rw [raw_spoke_hub_count_eq_card]
  congr 1
  symm
  apply Finset.card_bij (fun v _ => Sum.inr (false,v,u))
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    apply Finset.mem_filter.mpr
    constructor
    · simp [ordinaryCommonHubSpokeRoots,ordinaryHubSpokeRoots,ordinaryMarkedResourceEmbedding,
        orderedOrdinaryResourceEmbedding]
    · simpa [longRawHubState,typedMarkedResourceState,rawMarkedPairSpokes,
        rawExpandedApproximateCollapse] using hv
  · intro a ha b hb h
    exact (Prod.mk.inj (Prod.mk.inj (Sum.inr.inj h)).2).1
  · intro z hz
    simp only [Finset.mem_filter] at hz
    rcases Finset.mem_map.mp hz.1 with ⟨x,hx,rfl⟩
    rcases Finset.mem_image.mp hx with ⟨v,hv,rfl⟩
    refine ⟨v,?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      simpa [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding,longRawHubState,
        typedMarkedResourceState,rawMarkedPairSpokes,rawExpandedApproximateCollapse] using hz.2
    · rfl
end Oberwolfach
