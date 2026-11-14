module

public import Oberwolfach.LongRawMatchingAvoidsDeletedGraph
public import Oberwolfach.LongUsedSelectedDisjoint

@[expose] public section
/-! The surviving matching avoids both the original correction deletion
and any fixed reserve supported in the selected sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance survivingUsedAvoidsReserveFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_surviving_used_avoids_deletion_and_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (G Del Reserve:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hreserve:Reserve≤longSelectedPhysicalGraph G π d ω):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q);
    ∀x y,Used.Adj x y→¬(Del⊔Reserve).Adj x y:=by
  intro raw R T Q q φ M Used x y hu hDel
  have hav:=long_raw_surviving_matching_physical_rims_avoid_deleted_graph G Del π d m ℓ raw true true M
  have hdec:instDecidableEqFin n=survivingUsedAvoidsReserveFin n:=Subsingleton.elim _ _
  have hdecK:instDecidableEqFin K=survivingUsedAvoidsReserveFin K:=Subsingleton.elim _ _
  try rw [hdec,hdecK] at hav
  have hdel:¬Del.Adj x y:=by
    apply hav x y
    simpa only [Used,physicalRimCandidateUnion,Finset.mem_map,Finset.mem_filter,Finset.mem_univ] using hu
  have hdis:=long_used_sampled_matching_avoids_selected G π d ω true true
    (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)
  rcases hDel with hd|hr
  · exact hdel hd
  · exact (disjoint_iff_inf_le.mp hdis) ⟨hreserve hr,hu⟩
end Oberwolfach
