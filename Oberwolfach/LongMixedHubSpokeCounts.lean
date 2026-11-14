module

public import Oberwolfach.OrdinaryWheelHubSpokeCounts
public import Oberwolfach.MarkedWheelHubSpokeCounts
public import Oberwolfach.MarkedOrdinaryResourceLoads

@[expose] public section
/-! The hub-test sets in the common marked resource universe meet each
candidate in exactly the prescribed number of spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

def ordinaryCommonHubSpokeRoots (u:U):Finset (((V×V)⊕(V×V))⊕(Bool×V×U)):=
  (ordinaryHubSpokeRoots (V:=V) u).map ordinaryMarkedResourceEmbedding

theorem ordered_ordinary_common_hub_spoke_count
    (W:OrderedOrdinaryWheel (U:=U) π b r) (u:U):
    ((orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding∩ordinaryCommonHubSpokeRoots u).card=
      if W.2=u then r else 0 := by
  unfold ordinaryCommonHubSpokeRoots
  rw [←Finset.map_inter,Finset.card_map]
  exact ordered_ordinary_hub_spoke_count W u
end Oberwolfach
