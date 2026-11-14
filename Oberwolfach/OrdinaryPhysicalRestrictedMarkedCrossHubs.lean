module

public import Oberwolfach.OrdinaryPhysicalPayloadFiniteResources
public import Oberwolfach.OrdinaryPhysicalMatchingFiniteImages
public import Oberwolfach.OrdinaryPhysicalMarkedRestricted

@[expose] public section
/-! Distinct marked matching identifiers remain resource-disjoint after
restriction of their tuples to sampled arc types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_restricted_marked_cross_hubs (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState R H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (hL:∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources RR) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources RR) state y))
    (u v:U) (huv:u≠v) (a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u) (b:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L v)
    (A B:MarkedWheel (fun e:{e:Fin n×Fin n // R (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // R (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hAt:A.1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val)
    (hAh:A.2.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).2.val)
    (hBt:B.1.val=(ordinaryPhysicalMarkedPayload π d m RM state L v b).1.val)
    (hBh:B.2.val=(ordinaryPhysicalMarkedPayload π d m RM state L v b).2.val),
    Disjoint (markedWheelPhysicalResources A) (markedWheelPhysicalResources B) :=by
  intro RM state RR φ L hL u v huv a b A B hAt hAh hBt hBh
  have ha:a.val∈L:=(Finset.mem_filter.mp a.property).1
  have hb:b.val∈L:=(Finset.mem_filter.mp b.property).1
  have hne:a.val≠b.val:=by
    intro he
    have hu:ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent a.val.val.1 a.val.val.2=u:=
      (Finset.mem_filter.mp a.property).2.2
    have hv:ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent b.val.val.1 b.val.val.2=v:=
      (Finset.mem_filter.mp b.property).2.2
    rw [he] at hu
    exact huv (hu.symm.trans hv)
  have hdis:=physical_sampled_matching_images_disjoint φ (mixedCandidateResources RR) state L hL a.val ha b.val hb hne
  let f:=ordinaryPhysicalResourceToFinite (V:=Fin n) (U:=U)
  have hf:=ordinary_physical_resource_to_finite_injective (V:=Fin n) (U:=U)
  have hh:= (Finset.disjoint_image hf).mpr hdis
  have hcomp: f ∘ φ=markedSeedPhysicalMap (U:=U) π:=ordinary_physical_resource_to_finite_comp π
  have hres (w:U) (z:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L w):
      ((mixedCandidateResources RR z.val.val).image φ).image f =
      markedWheelPhysicalResources (ordinaryPhysicalMarkedRefinement π d m R H L w z):=by
    have hr:=ordinary_physical_marked_payload_resources π d m RM state L w z
    rw [hr,Finset.image_image,hcomp]
    have hz:=marked_seed_physical_resource_image π m (3*d) (ordinaryPhysicalMarkedPayload π d m RM state L w z)
    have he:=marked_wheel_same_tuple_same_physical_resources
      (ordinaryPhysicalMarkedPayload π d m RM state L w z)
      (ordinaryPhysicalMarkedRefinement π d m R H L w z) rfl rfl
    calc
      _ = markedWheelPhysicalResources (ordinaryPhysicalMarkedPayload π d m RM state L w z) := by
        convert hz using 1 <;> congr! 5 <;>
          (try (ext t; cases t <;> simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
      _ = _ := he.symm
  have hA:=marked_wheel_same_tuple_same_physical_resources (ordinaryPhysicalMarkedRefinement π d m R H L u a) A hAt hAh
  have hB:=marked_wheel_same_tuple_same_physical_resources (ordinaryPhysicalMarkedRefinement π d m R H L v b) B hBt hBh
  rw [hres u a,hres v b,←hA,←hB] at hh
  exact hh
end Oberwolfach
