module

public import Oberwolfach.OrdinaryMixedGenericFamily
public import Oberwolfach.OrdinaryShiftedPhysicalCandidateInjection
public import Oberwolfach.OrdinaryUnshiftedPhysicalCandidateInjection

@[expose] public section
/-! Each candidate of the generic mixed family has distinct physical
resources, although resources can coincide across different candidates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [LinearOrder V] [DecidableEq U]

theorem ordinary_mixed_generic_physical_injective
    (π:Equiv.Perm V) (b m:ℕ) (hm:2≤m) (hb:1≤b) (f:I→ℕ) (hf:∀i,1≤f i):
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π b (f i+2))=>orderedOrdinaryResources W);
    ∀i W,Set.InjOn (ordinaryMixedPhysicalResource (U:=U) π) (↑(R i W):Set _) :=by
  intro R i W
  cases i with
  | none=>
    simpa only [R,ordinaryMixedGenericResources] using ordinary_shifted_candidate_physical_injective hm hb W
  | some i=>
    simpa only [R,ordinaryMixedGenericResources] using ordinary_unshifted_candidate_physical_injective (by have hh:=hf i;omega) W
end Oberwolfach
