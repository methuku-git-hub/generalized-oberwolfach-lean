module

public import Oberwolfach.LongPhysicalResidualMatchingDegree
public import Oberwolfach.PhysicalRimSurvivingEmbedding

@[expose] public section
/-! The degree bound applies to the actual approximate rim graph after the
same deletion and matching, with no replacement of either witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_physical_residual_reference_bridge
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j;
    ∀(covered:Finset S) (a γ:ℝ),0≤γ→Fintype.card U≤n→
      (∀i,((longRawIncidenceSet S i\covered).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))→
      ∀x,(((physicalRimResidualGraph φ ∅\Del)\physicalRimCoveredGraph (f.trans φ) covered).degree x:ℝ)≤2*max a (4*γ)*n:=by
  intro T S f φ covered a γ hγ hu hmatch x
  have hSurvive:∀w:{z // z∈T},∀x y,φ w=Sum.inl s(x,y)→((∃z:{z // z∈S},f z=w)↔¬Del.Adj x y):=by
    intro w x y he
    have he':typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) w.val)=Sum.inl s(x,y):=he
    constructor
    · rintro ⟨z,hz⟩ hadj
      have hv:z.val=w.val:=congrArg Subtype.val hz
      have hz':=(Finset.mem_filter.mp z.property).2
      have hp:typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z.val)=Sum.inl s(x,y):=by
        rw [hv]
        exact he'
      rw [hp] at hz'
      exact hz' (SimpleGraph.mem_edgeFinset.mpr hadj)
    · intro hDel
      have hs:w.val∈S:=by
        apply Finset.mem_filter.mpr
        refine ⟨w.property,?_⟩
        rw [he']
        intro he
        exact hDel (SimpleGraph.mem_edgeFinset.mp he)
      refine ⟨⟨w.val,hs⟩,?_⟩
      exact Subtype.ext rfl
  have heq:=physical_rim_surviving_embedding_eq φ f Del hSurvive covered
  have hdegEq:(physicalRimResidualGraph (f.trans φ) covered).degree x=
      (((physicalRimResidualGraph φ ∅\Del)\physicalRimCoveredGraph (f.trans φ) covered).degree x):=by
    unfold SimpleGraph.degree
    congr 1
    ext v
    simp only [SimpleGraph.mem_neighborFinset]
    exact iff_of_eq (congrArg (fun G:SimpleGraph (Fin n)=>G.Adj x v) heq)
  rw [←hdegEq]
  exact long_physical_residual_matching_degree P Del π d raw g j covered a γ hγ hu hmatch x
end Oberwolfach
