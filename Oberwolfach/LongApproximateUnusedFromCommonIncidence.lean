module

public import Oberwolfach.LongPhysicalIncidenceMatchingBound
public import Oberwolfach.LongRawMatchingResidualAfterDeletion
public import Oberwolfach.LongApproximateResidualFromResources

@[expose] public section
/-! A surviving matching bounds the original physical approximate remainder;
the realised rim deletion contributes its maximum degree additively. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

theorem long_approximate_unused_degree_from_common_incidence
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (g j:Bool) (R:C→Finset (LongRawHubResource n U))
    (a γ δ:ℝ) (hγ:0≤γ) (hCardU:Fintype.card U≤n) (hD:∀x,(D.degree x:ℝ)≤δ):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    (∀i,((longRawIncidenceSet S i\M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀x,((longPhysicalStateGraph P σ {2,3}\physicalRimCandidateUnion φ
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)).degree x:ℝ)≤
        2*max a (4*γ)*n+δ+(6*d+2:ℕ) :=by
  intro raw T S f q φ M hmatch x
  let covered:Finset T:=(M.map q).biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈T)))
  have hcont:=long_approximate_unused_resource_containment P π d σ g j covered
  have hm:((longPhysicalStateGraph P σ {2,3}\physicalRimCoveredGraph φ covered).degree x:ℝ)≤
      ((physicalRimResidualGraph φ covered ⊔ longPreparationIneligibleGraph P π d).degree x:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hcont
  have hu:(((physicalRimResidualGraph φ covered ⊔ longPreparationIneligibleGraph P π d).degree x):ℝ)≤
      ((physicalRimResidualGraph φ covered).degree x:ℝ)+
        (longPreparationIneligibleGraph P π d).degree x:=by
    exact_mod_cast graph_degree_sup_le (physicalRimResidualGraph φ covered) (longPreparationIneligibleGraph P π d) x
  have hi:((longPreparationIneligibleGraph P π d).degree x:ℝ)≤(6*d+2:ℕ):=by
    exact_mod_cast long_preparation_ineligible_degree P π d x
  let coveredS:=M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))
  have hset:covered=coveredS.map f:=by
    exact surviving_candidate_covered_resources_lift R S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset) M
  have hm:((physicalRimResidualGraph φ (coveredS.map f)).degree x:ℝ)≤
      ((physicalRimResidualGraph (f.trans φ) coveredS ⊔ D).degree x:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le (long_raw_physical_residual_after_rim_deletion P D π d raw g j coveredS)
  have hs:(((physicalRimResidualGraph (f.trans φ) coveredS ⊔ D).degree x):ℝ)≤
      ((physicalRimResidualGraph (f.trans φ) coveredS).degree x:ℝ)+D.degree x:=by
    exact_mod_cast graph_degree_sup_le (physicalRimResidualGraph (f.trans φ) coveredS) D x
  have hr:((physicalRimResidualGraph (f.trans φ) coveredS).degree x:ℝ)≤
      ((rimIncidentResources (f.trans φ) x\coveredS).card:ℝ):=by
    exact_mod_cast physical_rim_residual_degree_le_uncovered (f.trans φ) coveredS x
  have hc:=long_physical_rim_incidence_from_matching_bounds P D π d raw g j coveredS a γ hγ hCardU hmatch x
  rw [←hset] at hm
  rw [←physical_rim_covered_eq_candidate_union φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)]
  linarith [hD x]
end Oberwolfach
