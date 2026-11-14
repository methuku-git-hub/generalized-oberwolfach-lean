module

public import Oberwolfach.LongRawMatchingRealizations
public import Oberwolfach.RealizationAvoidsReserved
public import Oberwolfach.LongClassApproximateAbsorberProtection

@[expose] public section
/-! Actual mixed-family wheel realizations preserve the fixed terminal absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawRealizationsAvoidAbsorberDecidableEqFin1 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_realizations_avoid_fixed_absorber
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U) (ℓ:Fin K→ℕ):
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false t J false false
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw true true)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw true true ℓ)
    let B:=fun z:Σi,LongRawRealizedWheel P π d m raw true true ℓ i=>
      longRawRealizedPhysicalResources P π d m raw true true ℓ z.1 z.2
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z→
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),∀c∈M,Disjoint (B (lift c)) Reserve :=by
  intro selected H raw state e R lift B habs M
  letI:∀i,Fintype (longRawSeedFamilies (U:=U) π d m ℓ i):=by
    intro i
    cases i with
    | none => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
    | some i => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
  letI:∀i,DecidableEq (longRawSeedFamilies (U:=U) π d m ℓ i):=fun _=>Classical.decEq _
  let C:=RestrictedResource (mixedCandidateResources R) e
  let Q:=restrictedResourceSet (mixedCandidateResources R) e
  let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw true true z)
  have havoid:Disjoint ((M.biUnion Q).image φ) Reserve:=
    long_class_matching_avoids_fixed_absorber P π d m σ t J Reserve X Z habs C Q M
  apply realization_avoids_reserved M Q φ lift B Reserve ?_ havoid
  intro c hc
  exact mixed_restricted_physical_lift_resources R e φ (longRawRealizeComponent P π d m raw true true ℓ)
    (longRawRealizedPhysicalResources P π d m raw true true ℓ)
    (long_raw_realize_component_resources P π d m raw true true ℓ) c
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawRealizationsAvoidAbsorberDecidableEqFin2 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_realized_resource_union
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ)
    let B:=longRawRealizedPhysicalResources P π d m raw g j ℓ
    let Q:=restrictedResourceSet (mixedCandidateResources R) e
    let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      (M.biUnion (fun c=>B (lift c).1 (lift c).2))=(M.biUnion Q).image φ :=by
  intro state e R lift B Q φ M
  letI:∀i,Fintype (longRawSeedFamilies (U:=U) π d m ℓ i):=by
    intro i
    cases i with
    | none => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
    | some i => dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
  letI:∀i,DecidableEq (longRawSeedFamilies (U:=U) π d m ℓ i):=fun _=>Classical.decEq _
  apply realization_resource_union M Q φ lift (fun z=>B z.1 z.2)
  intro c hc
  exact mixed_restricted_physical_lift_resources R e φ (longRawRealizeComponent P π d m raw g j ℓ)
    B (long_raw_realize_component_resources P π d m raw g j ℓ) c
end Oberwolfach
