module

public import Oberwolfach.LongPhysicalResidualReferenceBridge

@[expose] public section
/-! The unmatched approximate rim edges are sparse for the very matching
whose physical rim union is used in the factor packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_matching_residual_reference_bridge
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j;
    ∀(Q:C→Finset S) (M:Finset C) (a γ:ℝ),0≤γ→Fintype.card U≤n→
      (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))→
      ∀x,(((physicalRimResidualGraph φ ∅\Del)\physicalRimCandidateUnion (f.trans φ) Q M).degree x:ℝ)≤2*max a (4*γ)*n:=by
  intro T S f φ Q M a γ hγ hu hmatch x
  have heq:=physical_rim_covered_eq_candidate_union (f.trans φ) Q M
  have hdegEq:(((physicalRimResidualGraph φ ∅\Del)\physicalRimCoveredGraph (f.trans φ) (M.biUnion Q)).degree x)=
      (((physicalRimResidualGraph φ ∅\Del)\physicalRimCandidateUnion (f.trans φ) Q M).degree x):=by
    unfold SimpleGraph.degree
    congr 1
    ext v
    simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]
    rw [heq]
  rw [←hdegEq]
  exact long_physical_residual_reference_bridge P Del π d raw g j (M.biUnion Q) a γ hγ hu hmatch x
end Oberwolfach
