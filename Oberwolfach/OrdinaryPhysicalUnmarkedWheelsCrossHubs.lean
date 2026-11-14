module

public import Oberwolfach.OrdinaryPhysicalPayloadFiniteResources
public import Oberwolfach.OrdinaryPhysicalMatchingFiniteImages
public import Oberwolfach.OrdinaryPhysicalUnmarkedCrossHubs

@[expose] public section
/-! All unmarked wheels extracted from the same physical matching have
pairwise disjoint finite-set physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_unmarked_wheels_cross_hubs (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (u v:U) (huv:u≠v) (a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u) (b:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v),
    Disjoint (ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2)
      (ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L v b).2) :=by
  intro RM state RR φ L hL u v huv a b
  have hdis:=ordinary_physical_unmarked_cross_hubs π d m RM state L hL u v huv a b
  let f:=ordinaryPhysicalResourceToFinite (V:=Fin n) (U:=U)
  have hf:=ordinary_physical_resource_to_finite_injective (V:=Fin n) (U:=U)
  have hh:=(Finset.disjoint_image hf).mpr hdis
  have hcomp:f ∘ φ=markedSeedPhysicalMap (U:=U) π:=ordinary_physical_resource_to_finite_comp π
  have hres (w:U) (z:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L w):
      (((orderedOrdinaryResources (ordinaryPhysicalUnmarkedPayload π d m RM state L w z).2).map ordinaryMarkedResourceEmbedding).image φ).image f =
      ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L w z).2:=by
    rw [Finset.image_image,hcomp]
    have hz:=ordinary_seed_physical_resource_image π (3*d) _ (ordinaryPhysicalUnmarkedPayload π d m RM state L w z).2
    convert hz using 1 <;> congr! 5
  rw [hres u a,hres v b] at hh
  exact hh
end Oberwolfach
