module

public import Oberwolfach.OrdinaryPhysicalMixedPayloadDisjoint

@[expose] public section
/-! Exact finite-set physical resources of marked and ordinary payloads
extracted from their original matching identifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_marked_payload_finite_resources (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W);
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (u:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u),
    (mixedCandidateResources RR a.val.val).image (markedSeedPhysicalMap π)=
      markedWheelPhysicalResources (ordinaryPhysicalMarkedRefinement π d m R H L u a) :=by
  intro RM state RR L u a
  have h:=ordinary_physical_marked_payload_resources π d m RM state L u a
  rw [h]
  have hh:=marked_seed_physical_resource_image π m (3*d) (ordinaryPhysicalMarkedPayload π d m RM state L u a)
  have hsame:=marked_wheel_same_tuple_same_physical_resources
    (ordinaryPhysicalMarkedPayload π d m RM state L u a)
    (ordinaryPhysicalMarkedRefinement π d m R H L u a) rfl rfl
  calc
    _ = markedWheelPhysicalResources (ordinaryPhysicalMarkedPayload π d m RM state L u a) := by
      convert hh using 1 <;> congr! 5 <;>
        (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
    _ = _ := hsame.symm

theorem ordinary_physical_unmarked_payload_finite_resources (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W);
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (u:U) (a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u),
    (mixedCandidateResources RR a.val.val).image (markedSeedPhysicalMap π)=
      ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2 :=by
  intro RM state RR L u a
  have h:=ordinary_mixed_some_payload_resources RM
    (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩
  rw [h]
  have hh:=ordinary_seed_physical_resource_image π (3*d) _ (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
  convert hh using 1 <;> congr! 5
end Oberwolfach
