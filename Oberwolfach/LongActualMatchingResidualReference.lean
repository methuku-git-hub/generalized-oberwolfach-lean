module

public import Oberwolfach.LongMatchingResidualReferenceBridge
public import Oberwolfach.PhysicalRimCandidateNestedLift
public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! The residual-degree estimate uses the exact lifted matching and physical
rim union retained by the source-factor construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_actual_matching_residual_reference
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (R:C→Finset (LongRawHubResource n U)):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let eS:=Function.Embedding.subtype (·∈S)
    let eT:=Function.Embedding.subtype (·∈T)
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j;
    ∀(M:Finset (RestrictedResource R eS)) (a γ:ℝ),0≤γ→Fintype.card U≤n→
      (∀i,((longRawIncidenceSet S i\M.biUnion (restrictedResourceSet R eS)).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))→
      ∀x,(((physicalRimResidualGraph φ ∅\Del)\physicalRimCandidateUnion φ (restrictedResourceSet R eT) (M.map q)).degree x:ℝ)≤
        2*max a (4*γ)*n:=by
  intro T S f eS eT q φ M a γ hγ hu hmatch x
  have heq:=physical_rim_candidate_union_nested_lift R eS eT f (fun _=>rfl) φ M
  have hdegEq:(((physicalRimResidualGraph φ ∅\Del)\physicalRimCandidateUnion (f.trans φ) (restrictedResourceSet R eS) M).degree x)=
      (((physicalRimResidualGraph φ ∅\Del)\physicalRimCandidateUnion φ (restrictedResourceSet R eT) (M.map q)).degree x):=by
    unfold SimpleGraph.degree
    congr 1
    ext v
    simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]
    have hadj:(physicalRimCandidateUnion (f.trans φ) (restrictedResourceSet R eS) M).Adj x v ↔
        (physicalRimCandidateUnion φ (restrictedResourceSet R eT) (M.map q)).Adj x v:=
      iff_of_eq (congrArg (fun G:SimpleGraph (Fin n)=>G.Adj x v) heq)
    rw [hadj]
  rw [←hdegEq]
  exact long_matching_residual_reference_bridge P Del π d raw g j (restrictedResourceSet R eS) M a γ hγ hu hmatch x
end Oberwolfach
