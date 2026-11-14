module

public import Oberwolfach.LongUsedRawMixedDirection
public import Oberwolfach.LongUsedMixedEligibility
public import Oberwolfach.LongRawMatchingAvoidsDeletedGraph

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_surviving_matching_used_type_eligible
    (G S Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (Mhost:Fin n→Fin n→ℕ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hcorrect:∀x y,rawMixedPhysicalArc G π d raw x y→¬Del.Adj x y→Mhost x y=1):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState G π d raw g j)
    let Q:=longRawSurvivingResources G π d raw g j Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset G π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw g j
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)
    ∀x y,Mhost x y=1→Used.Adj x y→longOrdinaryArcEligible π d (x,y) ∨ longMarkedArcEligible π d (x,y):=by
  intro R T Q q φ M Used
  have hav:=long_raw_surviving_matching_physical_rims_avoid_deleted_graph G Del π d m ℓ raw g j M
  have hdir:=long_used_raw_mixed_direction G π d raw g j (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)
  have hav':∀x y,Used.Adj x y→¬Del.Adj x y:=by
    intro x y hu
    apply hav x y
    simpa only [Used,physicalRimCandidateUnion,Finset.mem_map,Finset.mem_filter,Finset.mem_univ] using hu
  have hdir':∀x y,Used.Adj x y→ rawMixedPhysicalArc G π d raw x y ∨ rawMixedPhysicalArc G π d raw y x:=by
    intro x y hu
    apply hdir x y
    simpa only [Used,physicalRimCandidateUnion,Finset.mem_map,Finset.mem_filter,Finset.mem_univ] using hu
  exact long_used_arc_eligible_from_mixed_orientation G S Used Del π d raw Mhost hphysical hcorrect hav' hdir' 
end Oberwolfach
