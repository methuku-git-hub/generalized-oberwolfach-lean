module

public import Oberwolfach.OrdinaryPhysicalRestrictedMarkedFamilyBasic
public import Oberwolfach.OrdinaryPhysicalRestrictedMixedPair
public import Oberwolfach.OrdinaryPhysicalPayloadFiniteResources
public import Oberwolfach.OrdinaryPhysicalMatchingFiniteImages

@[expose] public section
/-! The marked side of the physical matching can be realized on sampled
arc subtypes while preserving disjointness from all ordinary payloads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_restricted_marked_family (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (u:U),
    ∃W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true),
    (∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u) ∧
    (∀a b,a≠b→Disjoint (markedWheelPhysicalResources (W a)) (markedWheelPhysicalResources (W b))) ∧
    (∀a (b:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u),
      Disjoint (markedWheelPhysicalResources (W a))
        (ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u b).2)) :=by
  intro RM state RR φ L hL u
  obtain ⟨W,hW⟩:=ordinary_physical_restricted_marked_family_basic π d m R H L hL u
  have hhub (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u):
      (W a).2.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).2.val:=by
    exact (hW a).2.trans (ordinary_physical_marked_payload_hub π d m RM state L u a).symm
  refine ⟨W,hW,?_,?_⟩
  · intro a b hab
    exact ordinary_physical_restricted_marked_pair π d m R H L hL u a b hab (W a) (W b) (hW a).1 (hhub a) (hW b).1 (hhub b)
  · intro a b
    exact ordinary_physical_restricted_mixed_pair π d m R H L hL u a b (W a) (hW a).1 (hhub a)
end Oberwolfach
