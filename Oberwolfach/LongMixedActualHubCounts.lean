module

public import Oberwolfach.LongAssignedMixedSeedFamilies
public import Oberwolfach.LongMixedHubSpokeCounts
public import Oberwolfach.LongAssignedPaddedLengths

@[expose] public section
/-! The hub function and spoke counts for the actual mixed wheel families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def longMixedWheelHub (π:Equiv.Perm (Fin n)) (b m:ℕ):
    ∀j:Option (Fin K),LongMixedSeedFamily
      (MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True))
      (fun i=>OrderedOrdinaryWheel (U:=U) π b (longAssignedPaddedLength i)) j→U
  | none,W => W.2.val
  | some _,W => W.2

theorem long_mixed_ordinary_hub_spoke_count
    (π:Equiv.Perm (Fin n)) (b m:ℕ) (i:Fin K) (u:U)
    (W:OrderedOrdinaryWheel (U:=U) π b (longAssignedPaddedLength i)):
    let R:=longMixedSeedResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun _ (W:OrderedOrdinaryWheel (U:=U) π b (longAssignedPaddedLength _))=>orderedOrdinaryResources W)
    (R (some i) W∩ordinaryCommonHubSpokeRoots u).card=
      if longMixedWheelHub (U:=U) π b m (some i) W=u then longAssignedPaddedLength i else 0 :=by
  intro R
  convert ordered_ordinary_common_hub_spoke_count W u using 1
  congr 1
  ext x
  simp only [Finset.mem_inter]
  all_goals rfl
end Oberwolfach
