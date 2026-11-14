module

public import Oberwolfach.TypedMarkedCandidateRestriction
public import Oberwolfach.OrdinaryPhysicalMarkedRefinement

@[expose] public section
/-! Select a marked wheel on the sampled typed arc subtypes for every marked
identifier in the actual physical matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_marked_restricted_exists (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u),
    ∃W':MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true),
      W'.1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧
      W'.2.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).2.val :=by
  intro RM state L u a
  let W:=ordinaryPhysicalMarkedPayload π d m RM state L u a
  have hresource:=ordinary_physical_marked_payload_resources π d m RM state L u a
  have hsample:∀x∈typedMarkedOccurrenceResources W,typedMarkedResourceState R H x=true:=by
    intro x hx
    have hx':x∈mixedCandidateResources (ordinaryMixedGenericResources RM
      (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)) a.val.val:=by
      rw [hresource]
      exact hx
    exact a.val.property x hx'
  exact typed_marked_candidate_restriction W R H hsample
end Oberwolfach
