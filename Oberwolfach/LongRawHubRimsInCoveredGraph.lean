module

public import Oberwolfach.LongRawPhysicalHubRims
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! Every nonloop rim recorded at a hub belongs to the matching's covered graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longHubCoveredGraphFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_hub_rims_in_covered_graph
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀(M:Finset (RestrictedResource (mixedCandidateResources R) e)) (w:U) (x y:Fin n),
      x≠y→({x,y}:Finset (Fin n))∈longRawPhysicalHubRims P π d m ℓ raw g j M w→
      (physicalRimCandidateUnion φ (restrictedResourceSet (mixedCandidateResources R) e) M).Adj x y:=by
  intro state e R φ M w x y hxy h
  simp only [longRawPhysicalHubRims,physicalHubRims,Finset.mem_filter,Finset.mem_univ,true_and] at h
  obtain ⟨c,hc,_,hz⟩:=h
  obtain ⟨z,hz,hφ⟩:=Finset.mem_image.mp hz
  have hf:physicalResourceToFinite (φ z)=physicalResourceToFinite (Sum.inl s(x,y)):=by
    simp only [physicalResourceToFinite,Sum.map_inl,Sym2.toFinset_mk_eq]
    exact hφ
  have he:φ z=Sum.inl s(x,y):=physical_resource_to_finite_injective hf
  change x≠y ∧ ∃c∈M,∃z∈restrictedResourceSet (mixedCandidateResources R) e c,φ z=Sum.inl s(x,y)
  exact ⟨hxy,c,hc,z,hz,he⟩
end Oberwolfach
