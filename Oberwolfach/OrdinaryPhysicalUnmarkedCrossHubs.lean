module

public import Oberwolfach.OrdinaryPhysicalUnmarkedMatching

@[expose] public section
/-! Ordinary wheels selected at distinct hubs are disjoint in physical rim
and spoke resources, even though their candidate types are hub-indexed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_physical_unmarked_cross_hubs (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state)):
    let R:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    (∀x∈L,∀y∈L,x≠y→Disjoint (physicalSampledCandidateSet φ (mixedCandidateResources R) state x)
      (physicalSampledCandidateSet φ (mixedCandidateResources R) state y))→
    ∀(u v:U),u≠v→∀(a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u)
      (b:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v),
    Disjoint (((orderedOrdinaryResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2).map ordinaryMarkedResourceEmbedding).image φ)
      (((orderedOrdinaryResources (ordinaryPhysicalUnmarkedPayload π d m RM state L v b).2).map ordinaryMarkedResourceEmbedding).image φ) :=by
  intro R φ hL u v huv a b
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
  have hh:=physical_sampled_matching_images_disjoint φ (mixedCandidateResources R) state L hL a.val ha b.val hb hne
  have hA:=ordinary_physical_unmarked_payload_resources π d m RM state L u a
  have hB:=ordinary_physical_unmarked_payload_resources π d m RM state L v b
  have hA' : ((orderedOrdinaryResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2).map ordinaryMarkedResourceEmbedding).image φ =
      (mixedCandidateResources R a.val.val).image φ := by symm;convert hA using 1 <;> congr! 5
  have hB' : ((orderedOrdinaryResources (ordinaryPhysicalUnmarkedPayload π d m RM state L v b).2).map ordinaryMarkedResourceEmbedding).image φ =
      (mixedCandidateResources R b.val.val).image φ := by symm;convert hB using 1 <;> congr! 5
  rw [hA',hB']
  exact hh
end Oberwolfach
