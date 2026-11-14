module

public import Oberwolfach.LongRawMatchingRealizations
public import Oberwolfach.LongMixedHubSpokeCounts

@[expose] public section
/-! The original mixed candidate family has exactly one ordinary spoke per
rim vertex at its own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawHubCountFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_ordinary_hub_spoke_count
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (i:Fin K) (u:U)
    (W:longRawSeedFamilies (U:=U) π d m ℓ (some i)):
    (longRawSeedResources (U:=U) π d m ℓ (some i) W∩ordinaryCommonHubSpokeRoots u).card=
      if longRawSeedHub π d m ℓ (some i) W=u then ℓ i else 0 :=by
  convert ordered_ordinary_common_hub_spoke_count W u using 1 <;>
    congr 1 <;> ext z <;> simp only [longRawSeedResources,longMixedSeedResources,
      Finset.mem_inter,Finset.mem_map,orderedOrdinaryResources,Finset.mem_union,Finset.mem_image]
end Oberwolfach
