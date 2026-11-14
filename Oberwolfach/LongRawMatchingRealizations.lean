module

public import Oberwolfach.LongMixedRawHubPreservation

@[expose] public section
/-! The selected raw mixed-family resource matching gives distinct,
physically edge-disjoint wheel realizations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawMatchingRealizationsDecidableEqFin1 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_matching_realizations
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=longRawRealizeComponent P π d m raw g j ℓ
    let B:=longRawRealizedPhysicalResources P π d m raw g j ℓ
    ∀(w:∀i,longRawSeedFamilies (U:=U) π d m ℓ i→ℝ)
      (M:Finset (RestrictedResource (mixedCandidateResources R) e)),
    (∀i c,0<w i c→1≤(R i c).card) →
    (∀c∈M,0<mixedCandidateWeight w c.val) →
    (∀c∈M,∀d∈M,c≠d→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e d)) →
    (∀c∈M,∀d∈M,c≠d→Disjoint
      (B (mixedRestrictedPhysicalLift R e lift c).1 (mixedRestrictedPhysicalLift R e lift c).2)
      (B (mixedRestrictedPhysicalLift R e lift d).1 (mixedRestrictedPhysicalLift R e lift d).2)) ∧
    Set.InjOn (mixedRestrictedPhysicalLift R e lift) (↑M:Set _) :=by
  intro state e φ R lift B w M hsize hpos hmatch
  letI:∀i,Fintype (longRawSeedFamilies (U:=U) π d m ℓ i):=by
    intro i
    cases i with
    | none => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
    | some i => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
  letI:∀i,DecidableEq (longRawSeedFamilies (U:=U) π d m ℓ i):=fun _=>Classical.decEq _
  have hφ:Function.Injective φ:=physical_resource_to_finite_injective.comp
    (markedRawSampledPhysicalEmbedding P π d raw g j).injective
  apply mixed_positive_matching_physical_realizations R e φ hφ lift B ?_ w hsize M hpos hmatch
  intro i c
  exact long_raw_realize_component_resources P π d m raw g j ℓ i c
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawMatchingRealizationsDecidableEqFin2 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_matching_realization_preserves_hub
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=longRawRealizeComponent P π d m raw g j ℓ
    ∀c:RestrictedResource (mixedCandidateResources R) e,
      longRawRealizedHub P π d m raw g j ℓ (mixedRestrictedPhysicalLift R e lift c).1
        (mixedRestrictedPhysicalLift R e lift c).2 = longRawSeedHub π d m ℓ c.val.1 c.val.2 :=by
  intro state e R lift c
  exact long_raw_realize_component_hub P π d m raw g j ℓ c.val.1 ((mixedRestrictedFamilyEquiv R e c).2)
end Oberwolfach
