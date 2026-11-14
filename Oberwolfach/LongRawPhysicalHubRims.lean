module

public import Oberwolfach.LongRawSelectedMarkedHub
public import Oberwolfach.PhysicalHubPacking

@[expose] public section
/-! Split the actual mixed matching's physical rim resources by their
original hub; the resulting sets are disjoint across distinct hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawPhysicalHubDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def longRawPhysicalHubRims
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),U→Finset (Finset (Fin n)):=by
  intro state e R M w
  let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
  exact physicalHubRims M (fun c=>longRawSeedHub π d m ℓ c.val.1 c.val.2)
    (fun c=>(restrictedResourceSet (mixedCandidateResources R) e c).image φ) w

theorem long_raw_physical_hub_rims_packed
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    ∀w z,w≠z→Disjoint (longRawPhysicalHubRims P π d m ℓ raw g j M w)
      (longRawPhysicalHubRims P π d m ℓ raw g j M z):=by
  intro state e R M hmatch
  let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
  have hφ:Function.Injective φ:=physical_resource_to_finite_injective.comp
    (markedRawSampledPhysicalEmbedding P π d raw g j).injective
  have hpack:∀c∈M,∀c'∈M,c≠c'→Disjoint
      ((restrictedResourceSet (mixedCandidateResources R) e c).image φ)
      ((restrictedResourceSet (mixedCandidateResources R) e c').image φ):=by
    intro c hc c' hc' hne
    exact (Finset.disjoint_image hφ).mpr (hmatch c hc c' hc' hne)
  exact (physical_hub_rims_packed M (fun c=>longRawSeedHub π d m ℓ c.val.1 c.val.2)
    (fun c=>(restrictedResourceSet (mixedCandidateResources R) e c).image φ) hpack).1
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawPhysicalHubDecEqFin2 (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_realized_rim_in_its_hub
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ)
    let B:=fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>longRawRealizedPhysicalResources P π d m raw g j ℓ z.1 z.2
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),∀c∈M,∀x:Finset (Fin n),
      Sum.inl x∈B (lift c)→x∈longRawPhysicalHubRims P π d m ℓ raw g j M (longRawSeedHub π d m ℓ c.val.1 c.val.2):=by
  intro state e R lift B M c hc x hx
  letI:∀i,Fintype (longRawSeedFamilies (U:=U) π d m ℓ i):=by
    intro i
    cases i with
    | none=>dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
    | some i=>dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
  letI:∀i,DecidableEq (longRawSeedFamilies (U:=U) π d m ℓ i):=fun _=>Classical.decEq _
  let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
  have heq:=mixed_restricted_physical_lift_resources R e φ (longRawRealizeComponent P π d m raw g j ℓ)
    (longRawRealizedPhysicalResources P π d m raw g j ℓ)
    (long_raw_realize_component_resources P π d m raw g j ℓ) c
  have hx':Sum.inl x∈(restrictedResourceSet (mixedCandidateResources R) e c).image φ:=by
    rw [←heq]
    exact hx
  change x∈physicalHubRims M (fun c=>longRawSeedHub π d m ℓ c.val.1 c.val.2)
    (fun c=>(restrictedResourceSet (mixedCandidateResources R) e c).image φ) _
  simp only [physicalHubRims,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨c,hc,rfl,hx'⟩
end Oberwolfach
