module

public import Oberwolfach.OrdinaryPhysicalRestrictedMarkedPair
public import Oberwolfach.OrdinaryPhysicalMixedPayloadCrossHubs

@[expose] public section
/-! Restricting a marked tuple to its sampled arc subtypes preserves its
physical disjointness from every selected ordinary wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_restricted_mixed_cross_hubs (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (u v:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u)
    (b:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v)
    (A:MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hAt:A.1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val)
    (hAh:A.2.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).2.val),
    Disjoint (markedWheelPhysicalResources A)
      (ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L v b).2) :=by
  intro RM state RR φ L hL u v a b A hAt hAh
  have hA:=marked_wheel_same_tuple_same_physical_resources (ordinaryPhysicalMarkedRefinement π d m R H L u a) A hAt hAh
  rw [hA]
  exact ordinary_physical_mixed_payload_disjoint_hubs π d m R H L hL u v a b
end Oberwolfach
