module

public import Oberwolfach.OrdinaryPhysicalPayloadFiniteResources
public import Oberwolfach.OrdinaryPhysicalMatchingRows

@[expose] public section

/-! A physical spoke in a selected mixed candidate determines that
candidate's hub, for either kind of wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_candidate_spoke_hub
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(c:PhysicalSampledCandidate (mixedCandidateResources RR) state)
      (x:PhysicalSampledActive φ state) (v:Fin n) (u:U),
      x.val=Sum.inr (v,u)→x∈physicalSampledCandidateSet φ (mixedCandidateResources RR) state c→
      ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent c.val.1 c.val.2=u :=by
  intro RM state RR φ c x v u hx hc
  have hm:x.val∈(mixedCandidateResources RR c.val).image φ:=
    (physical_sampled_candidate_set_mem φ (mixedCandidateResources RR) state c x).mp hc
  obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hm
  have hphys:Sum.inr (v,u)∈(mixedCandidateResources RR c.val).image (markedSeedPhysicalMap π):=by
    apply Finset.mem_image.mpr
    refine ⟨a,ha,?_⟩
    rw [←ordinary_physical_resource_to_finite_comp π]
    change ordinaryPhysicalResourceToFinite (φ a)=Sum.inr (v,u)
    rw [he,hx]
    rfl
  by_cases hnone:c.val.1.isNone
  ·
    let z:{v:(type_of% c.val) // v.1.isNone}:=⟨c.val,hnone⟩
    let W:=ordinaryMixedNonePayload z
    have horig:=ordinary_mixed_none_payload_original z
    have hres:mixedCandidateResources RR c.val=typedMarkedOccurrenceResources W:=by rw [horig];rfl
    rw [hres] at hphys
    have hh:=marked_seed_physical_resource_image π m (3*d) W
    have heq:(typedMarkedOccurrenceResources W).image (markedSeedPhysicalMap π)=markedWheelPhysicalResources W:=by
      convert hh using 1 <;> congr! 5 <;>
        (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
    rw [heq] at hphys
    have hhub:W.2.val=u:=((markedWheelPhysicalResources_spoke W v u).mp hphys).1
    rw [horig]
    exact hhub
  ·
    have hsome:c.val.1.isSome:=by
      cases hh:c.val.1 <;> simp_all
    let z:{v:(type_of% c.val) // v.1.isSome}:=⟨c.val,hsome⟩
    let W:=ordinaryMixedSomePayload z
    have horig:=ordinary_mixed_some_payload_original z
    have hres:=ordinary_mixed_some_payload_resources RM
      (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W) z
    change mixedCandidateResources RR c.val=(orderedOrdinaryResources W.2).map ordinaryMarkedResourceEmbedding at hres
    rw [hres] at hphys
    have hh:=ordinary_seed_physical_resource_image π (3*d) _ W.2
    have heq:((orderedOrdinaryResources W.2).map ordinaryMarkedResourceEmbedding).image (markedSeedPhysicalMap π)=
        ordinaryWheelPhysicalResources W.2:=by convert hh using 1 <;> congr! 5
    rw [heq] at hphys
    have hex:∃j,W.2.1.val j=v ∧ W.2.2=u:=by simpa [ordinaryWheelPhysicalResources] using hphys
    obtain ⟨j,hv,hhub⟩:=hex
    rw [horig]
    exact hhub
end Oberwolfach
