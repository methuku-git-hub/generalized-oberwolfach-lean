module

public import Oberwolfach.OrdinaryPhysicalUnmarkedPayload
public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber

@[expose] public section
/-! The same selected candidate identifiers give disjoint physical ordinary
wheel resource sets after extracting their unmarked payloads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_unmarked_payload_resources (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U) (a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u):
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let payload:=ordinaryPhysicalUnmarkedPayload π d m RM state L u a;
    (mixedCandidateResources R a.val.val).image (ordinaryMixedPhysicalResource π)=
      ((orderedOrdinaryResources payload.2).map ordinaryMarkedResourceEmbedding).image (ordinaryMixedPhysicalResource π) :=by
  intro R payload
  have hh:=ordinary_mixed_some_payload_resources RM
    (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    ⟨a.val.val,(Finset.mem_filter.mp a.property).2.1⟩
  convert congrArg (fun S=>S.image (ordinaryMixedPhysicalResource (U:=U) π)) hh using 1 <;> congr! 5

theorem ordinary_physical_unmarked_payload_matching (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (u:U):
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let payload:=ordinaryPhysicalUnmarkedPayload π d m RM state L u;
    (∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources R) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources R) state y))→
    ∀a b:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u,a≠b→
      Disjoint (((orderedOrdinaryResources (payload a).2).map ordinaryMarkedResourceEmbedding).image φ)
        (((orderedOrdinaryResources (payload b).2).map ordinaryMarkedResourceEmbedding).image φ) :=by
  intro R φ payload hL a b hab
  have ha:a.val∈L:=(Finset.mem_filter.mp a.property).1
  have hb:b.val∈L:=(Finset.mem_filter.mp b.property).1
  have hne:a.val≠b.val:=fun h=>hab (Subtype.ext h)
  have hh:=physical_sampled_matching_images_disjoint φ (mixedCandidateResources R) state L hL a.val ha b.val hb hne
  have hA:=ordinary_physical_unmarked_payload_resources π d m RM state L u a
  have hB:=ordinary_physical_unmarked_payload_resources π d m RM state L u b
  have hA' : ((orderedOrdinaryResources (payload a).2).map ordinaryMarkedResourceEmbedding).image φ =
      (mixedCandidateResources R a.val.val).image φ := by
    symm
    convert hA using 1 <;> congr! 5
  have hB' : ((orderedOrdinaryResources (payload b).2).map ordinaryMarkedResourceEmbedding).image φ =
      (mixedCandidateResources R b.val.val).image φ := by
    symm
    convert hB using 1 <;> congr! 5
  rw [hA',hB']
  exact hh
end Oberwolfach
