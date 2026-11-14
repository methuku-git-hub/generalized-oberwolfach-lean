module

public import Oberwolfach.OrdinaryPhysicalMarkedRefinement
public import Oberwolfach.OrdinaryPhysicalUnmarkedMatching
public import Oberwolfach.OrdinaryPhysicalResourceToFinite
public import Oberwolfach.MarkedWheelTuplePhysicalInvariant

@[expose] public section
/-! The marked and ordinary wheels extracted from the same physical matching
have disjoint finite-set physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_mixed_payload_disjoint (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (u:U) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u)
    (b:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u),
    Disjoint (markedWheelPhysicalResources (ordinaryPhysicalMarkedRefinement π d m R H L u a))
      (ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u b).2) :=by
  intro RM state RR φ L hL u a b
  have ha:a.val∈L:=(Finset.mem_filter.mp a.property).1
  have hb:b.val∈L:=(Finset.mem_filter.mp b.property).1
  have hne:a.val≠b.val:=by
    intro heq
    have hn: a.val.val.1.isNone:=(Finset.mem_filter.mp a.property).2.1
    have hs: b.val.val.1.isSome:=(Finset.mem_filter.mp b.property).2.1
    rw [heq] at hn
    cases h:b.val.val.1 <;> simp_all
  have hdis:=physical_sampled_matching_images_disjoint φ (mixedCandidateResources RR) state L hL a.val ha b.val hb hne
  let f:=ordinaryPhysicalResourceToFinite (V:=Fin n) (U:=U)
  have hf:=ordinary_physical_resource_to_finite_injective (V:=Fin n) (U:=U)
  have hdis':= (Finset.disjoint_image hf).mpr hdis
  have hcomp: f ∘ φ=markedSeedPhysicalMap (U:=U) π:=ordinary_physical_resource_to_finite_comp π
  have hmarked:((mixedCandidateResources RR a.val.val).image φ).image f =
      markedWheelPhysicalResources (ordinaryPhysicalMarkedRefinement π d m R H L u a):=by
    have hres:=ordinary_physical_marked_payload_resources π d m RM state L u a
    rw [hres,Finset.image_image,hcomp]
    have hh:=marked_seed_physical_resource_image π m (3*d) (ordinaryPhysicalMarkedPayload π d m RM state L u a)
    have hsame:=marked_wheel_same_tuple_same_physical_resources
      (ordinaryPhysicalMarkedPayload π d m RM state L u a)
      (ordinaryPhysicalMarkedRefinement π d m R H L u a) rfl rfl
    calc
      _ = markedWheelPhysicalResources (ordinaryPhysicalMarkedPayload π d m RM state L u a) := by
        convert hh using 1 <;> congr! 5 <;>
          (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
      _ = _ := hsame.symm
  have hord:((mixedCandidateResources RR b.val.val).image φ).image f =
      ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u b).2:=by
    have hres:=ordinary_mixed_some_payload_resources RM
      (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
      ⟨b.val.val,(Finset.mem_filter.mp b.property).2.1⟩
    rw [hres,Finset.image_image,hcomp]
    have hh:=ordinary_seed_physical_resource_image π (3*d) _ (ordinaryPhysicalUnmarkedPayload π d m RM state L u b).2
    convert hh using 1 <;> congr! 5
  rw [hmarked,hord] at hdis'
  exact hdis'
end Oberwolfach
