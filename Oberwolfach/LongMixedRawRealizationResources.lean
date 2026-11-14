module

public import Oberwolfach.LongMixedRawRealizationDef

@[expose] public section
/-! The mixed realizations preserve all physical rim and spoke resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMixedRawRealizationResourcesDecidableEqFin1 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_realize_component_resources
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
    ∀i W,longRawRealizedPhysicalResources P π d m raw g j ℓ i
        (longRawRealizeComponent P π d m raw g j ℓ i W)=
      (restrictedResourceSet (longRawSeedResources (U:=U) π d m ℓ i) e W).image φ :=by
  intro state e φ i W
  cases i with
  | none =>
    have hset : (restrictedResourceSet (longRawSeedResources (U:=U) π d m ℓ none) e W).image φ =
        (restrictedResourceSet (fun C:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
          (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources C) e
          (longRawMarkedComponent π d m ℓ e W)).image φ := by
      congr 1 <;> ext x <;>
      simp only [restrictedResourceSet,Finset.mem_filter,Finset.mem_univ,true_and] <;>
      simp only [longRawSeedResources,longMixedSeedResources,longRawMarkedComponent,
        typedMarkedOccurrenceResources,Finset.mem_union,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hset]
    simpa only [longRawRealizedPhysicalResources,longRawRealizeComponent] using
      (raw_marked_realization_properties P π d m raw g j
        (longRawMarkedComponent π d m ℓ e W)).2.2.symm
  | some i =>
    have hset : (restrictedResourceSet (longRawSeedResources (U:=U) π d m ℓ (some i)) e W).image φ =
        (restrictedResourceSet (fun C:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ i)=>
          (orderedOrdinaryResources C).map ordinaryMarkedResourceEmbedding) e
          (longRawOrdinaryComponent π d m ℓ i e W)).image φ := by
      congr 1 <;> ext x <;>
      simp only [restrictedResourceSet,Finset.mem_filter,Finset.mem_univ,true_and] <;>
      simp only [longRawSeedResources,longMixedSeedResources,longRawOrdinaryComponent,
        Finset.mem_map,orderedOrdinaryResources,Finset.mem_union,Finset.mem_image] <;> try rfl
    rw [hset]
    exact (raw_restricted_ordinary_candidate_physical_lift P π d (ℓ i) raw g j
      (longRawOrdinaryComponent π d m ℓ i e W)).symm
end Oberwolfach
