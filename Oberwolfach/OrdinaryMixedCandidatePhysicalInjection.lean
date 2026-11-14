module

public import Oberwolfach.OrdinaryShiftedPhysicalCandidateInjection
public import Oberwolfach.OrdinaryUnshiftedPhysicalCandidateInjection
public import Oberwolfach.LongAssignedMixedSeedFamilies

@[expose] public section
/-! Every member of the mixed candidate family has distinct physical
resources, for both the shifted and unshifted families. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) mixedInjectionFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_mixed_candidate_physical_injective
    (π:Equiv.Perm (Fin n)) (b m:ℕ) (hm:2≤m) (hb:1≤b)
    (ℓ:Fin K→ℕ) (hℓ:∀i,2≤ℓ i):
    let R:=longMixedSeedResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π b (ℓ i+1))=>orderedOrdinaryResources W);
    ∀i W,Set.InjOn (ordinaryMixedPhysicalResource (U:=U) π) (↑(R i W):Set _) :=by
  intro R i W
  cases i with
  | none=>
    simpa only [R,longMixedSeedResources] using ordinary_shifted_candidate_physical_injective hm hb W
  | some i=>
    simpa only [R,longMixedSeedResources] using ordinary_unshifted_candidate_physical_injective (by have hh:=hℓ i;omega) W
end Oberwolfach
