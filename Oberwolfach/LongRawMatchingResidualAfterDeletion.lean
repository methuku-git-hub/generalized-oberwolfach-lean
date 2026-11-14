module

public import Oberwolfach.LongRawPhysicalResidualAfterDeletion
public import Oberwolfach.SurvivingMatchingCoverageLift

@[expose] public section
/-! Lift one matching and its covered physical resources from a later
rim-deleted state to the original sample, charging the deletion directly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

theorem long_raw_matching_residual_degree_after_rim_deletion
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (R:C→Finset (LongRawHubResource n U)) (a γ δ:ℝ) (hγ:0≤γ)
    (hD:∀x,(D.degree x:ℝ)≤δ):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    (∀x,a*n≤(rimIncidentResources (f.trans φ) x).card →
      (((rimIncidentResources (f.trans φ) x\M.biUnion
        (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℕ):ℝ)≤
          γ*(rimIncidentResources (f.trans φ) x).card) →
    ∀x,((physicalRimResidualGraph φ ((M.map q).biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤
        max a γ*n+δ :=by
  intro T S f q φ M hlarge x
  have hset:((M.map q).biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈T)))) =
      (M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).map f :=by
    exact surviving_candidate_covered_resources_lift R S T _ M
  rw [hset]
  let covered:=M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))
  have hm:((physicalRimResidualGraph φ (covered.map f)).degree x:ℝ)≤
      ((physicalRimResidualGraph (f.trans φ) covered ⊔ D).degree x:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le
      (long_raw_physical_residual_after_rim_deletion P D π d raw g j covered)
  have hu:(((physicalRimResidualGraph (f.trans φ) covered ⊔ D).degree x):ℝ)≤
      ((physicalRimResidualGraph (f.trans φ) covered).degree x:ℝ)+D.degree x:=by
    exact_mod_cast graph_degree_sup_le (physicalRimResidualGraph (f.trans φ) covered) D x
  have hr:=physical_rim_residual_degree_from_large_coverage (f.trans φ) covered a γ hγ (by simpa using hlarge) x
  simp only [Fintype.card_fin] at hr
  linarith [hD x]
end Oberwolfach
