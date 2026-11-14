module

public import Oberwolfach.LongMixedHubSpokeCounts

@[expose] public section
/-! A fixed hub has exactly one ordinary typed spoke root per vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_common_hub_roots_card (u:U):
    (ordinaryCommonHubSpokeRoots (V:=V) u).card=Fintype.card V :=by
  unfold ordinaryCommonHubSpokeRoots ordinaryHubSpokeRoots
  rw [Finset.card_map,Finset.card_image_of_injective]
  · simp
  · intro x y h
    exact Prod.mk.inj (Sum.inr.inj h) |>.1

theorem ordinary_common_hub_active_roots_card_le (u:U)
    (state:(((V×V)⊕(V×V))⊕(Bool×V×U))→Bool):
    ((ordinaryCommonHubSpokeRoots (V:=V) u).filter (fun z=>state z=true)).card≤Fintype.card V :=by
  calc
    _ ≤ (ordinaryCommonHubSpokeRoots (V:=V) u).card:=Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card V:=ordinary_common_hub_roots_card u
end Oberwolfach
