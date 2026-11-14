module

public import Oberwolfach.LongRawHubRimsInCoveredGraph

@[expose] public section
/-! The packing set used by the old-source interface is the entire set of
matching-allocated rim edges.  Its containment of the embedded old edges is
one-sided; equality with the embedded edges needs a separate argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchingAllocationEqualsUsedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matching_allocation_equals_used
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀(M:Finset (RestrictedResource (mixedCandidateResources R) e)),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet (mixedCandidateResources R) e) M
    let Alloc:=Finset.univ.filter (fun a:Sym2 (Fin n)=>a.toFinset∈Finset.univ.biUnion (longRawPhysicalHubRims P π d m ℓ raw g j M))
    (∀a∈Alloc,a∈Used.edgeFinset)→Alloc=Used.edgeFinset:=by
  intro state e R φ M Used Alloc hsubset
  apply Finset.Subset.antisymm hsubset
  intro a ha
  induction a using Sym2.ind with
  | _ x y =>
    have hh:Used.Adj x y:=SimpleGraph.mem_edgeFinset.mp ha
    change x≠y ∧ ∃c∈M,∃z∈restrictedResourceSet (mixedCandidateResources R) e c,φ z=Sum.inl s(x,y) at hh
    obtain ⟨_,c,hc,z,hz,hφ⟩:=hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨longRawSeedHub π d m ℓ c.val.1 c.val.2,Finset.mem_univ _,?_⟩⟩
    rw [Sym2.toFinset_mk_eq]
    change ({x,y}:Finset (Fin n))∈physicalHubRims M (fun c=>longRawSeedHub π d m ℓ c.val.1 c.val.2)
      (fun c=>(restrictedResourceSet (mixedCandidateResources R) e c).image (fun z=>physicalResourceToFinite (φ z))) _
    simp only [physicalHubRims,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨c,hc,rfl,Finset.mem_image.mpr ⟨z,hz,?_⟩⟩
    rw [hφ]
    simp only [physicalResourceToFinite,Sum.map_inl,Sym2.toFinset_mk_eq]
end Oberwolfach
