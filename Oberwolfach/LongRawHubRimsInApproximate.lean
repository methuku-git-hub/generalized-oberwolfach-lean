module

public import Oberwolfach.LongRawPhysicalHubRims
public import Oberwolfach.RawApproximateEmbeddingLayer

@[expose] public section
/-! Every matching rim resource comes from an actual edge of the same
approximate physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawHubRimsApproxDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_hub_rims_in_approximate_graph
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (g j:Bool):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),∀w x,
      x∈longRawPhysicalHubRims P π d m ℓ raw g j M w→
      ∃a∈(longApproximatePhysicalGraph P π d σ).edgeFinset,a.toFinset=x:=by
  intro raw state e R M w x hx
  simp only [longRawPhysicalHubRims,physicalHubRims,Finset.mem_filter,Finset.mem_univ,true_and] at hx
  obtain ⟨c,hc,hcw,hr⟩:=hx
  obtain ⟨z,hz,hzx⟩:=Finset.mem_image.mp hr
  have hφ:=raw_sampled_physical_embedding_in_approximate_layer P π d σ g j z
  change markedRawSampledPhysicalEmbedding P π d raw g j z∈
    wheelLayerPhysicalResources (longApproximatePhysicalGraph P π d σ)
      (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j) at hφ
  cases hval:markedRawSampledPhysicalEmbedding P π d raw g j z with
  | inl a=>
    rw [hval] at hφ hzx
    have ha:a∈(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
      simpa [wheelLayerPhysicalResources] using hφ
    have heq:a.toFinset=x:=by simpa [physicalResourceToFinite] using hzx
    exact ⟨a,ha,heq⟩
  | inr b=>
    rw [hval] at hzx
    simp [physicalResourceToFinite] at hzx
theorem long_raw_hub_rim_union_pack_in_approximate_graph
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (g j:Bool):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      (Finset.univ.filter (fun a:Sym2 (Fin n)=>a.toFinset∈
        Finset.univ.biUnion (longRawPhysicalHubRims P π d m ℓ raw g j M)))⊆
        (longApproximatePhysicalGraph P π d σ).edgeFinset:=by
  intro raw state e R M a ha
  obtain ⟨w,_,hw⟩:=Finset.mem_biUnion.mp ((Finset.mem_filter.mp ha).2)
  obtain ⟨b,hb,hba⟩:=long_raw_hub_rims_in_approximate_graph P π d m ℓ σ g j M w a.toFinset hw
  have he:physicalResourceToFinite (U:=U) (Sum.inl b)=physicalResourceToFinite (Sum.inl a):=by
    simp only [physicalResourceToFinite,Sum.map_inl]
    exact congrArg Sum.inl hba
  have hab:b=a:=Sum.inl.inj (physical_resource_to_finite_injective he)
  simpa only [hab] using hb
end Oberwolfach
