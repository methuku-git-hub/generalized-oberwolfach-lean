module

public import Oberwolfach.OrdinaryMarkedSampledSpokes

@[expose] public section
/-! Each selected marked identifier yields an actual wheel with the sampled
spoke conditions, without changing its cycle or hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def ordinaryPhysicalMarkedRefinement (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u),
    MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d) (H false) (H true) :=by
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
  have hspokes:=typed_marked_sampled_spoke_compatibility W R H hsample
  exact ⟨W.1,⟨W.2.val,hspokes⟩⟩
end Oberwolfach
