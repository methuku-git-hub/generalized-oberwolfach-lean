module

public import Oberwolfach.LongResidualSurplusDegreeBound
public import Oberwolfach.GraphDifferenceChangedDegree
public import Oberwolfach.LongPhysicalStateDegree

@[expose] public section
/-! The common event's unassigned colour degree and class-edit bound provide
the remaining inputs for the full residual surplus estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_surplus_from_common_event
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (P S Small Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (g j:Bool) (R:C→Finset (LongRawHubResource n U)) (a γ δ ξ θ u err:ℝ)
    (hγ:0≤γ) (hCardU:Fintype.card U≤n) (hDel:∀x,(Del.degree x:ℝ)≤δ)
    (hθ:0≤θ) (hu:u≤2*θ)
    (hcolour:∀x,|((sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) 4 x):ℝ)-u*(P.degree x:ℝ)|≤err)
    (hEdit:∀x,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset x) (S.neighborFinset x)).card:ℝ)≤ξ*n):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let Q:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j;
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q);
    Used≤Small→
    (∀i,((longRawIncidenceSet Q i\M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Q)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet Q i).card))→
    ∀x,((((S\Small)\longSelectedPhysicalGraph P π d σ).degree x):ℝ)≤
      2*θ*n+err+2*max a (4*γ)*n+δ+2*(6*d+2:ℕ)+ξ*n:=by
  have h4:∀x,((longPhysicalStateGraph P σ {4}).degree x:ℝ)≤2*θ*n+err:=by
    intro x
    have hp:(P.degree x:ℝ)≤n:=by
      have hn:P.degree x≤n:=by simpa only [Fintype.card_fin] using (P.degree_lt_card_verts x).le
      exact_mod_cast hn
    have hmul:u*(P.degree x:ℝ)≤2*θ*n:=by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0≤(P.degree x:ℝ) by positivity),
        mul_nonneg hθ (sub_nonneg.mpr hp)]
    have hc:((sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) 4 x):ℝ)≤u*(P.degree x:ℝ)+err:=by
      have hh:=(abs_le.mp (hcolour x)).2
      linarith
    rw [long_physical_state_singleton_degree]
    linarith
  have hedit:∀x,((S\longPhysicalStateGraph P σ {0,1,2,3,4}).degree x:ℝ)≤ξ*n:=by
    intro x
    have hnat:=graph_difference_degree_le_changed S (longPhysicalStateGraph P σ {0,1,2,3,4}) x
    have hh:((S\longPhysicalStateGraph P σ {0,1,2,3,4}).degree x:ℝ)≤
        (changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset x) (S.neighborFinset x)).card:=by
      exact_mod_cast hnat
    exact hh.trans (hEdit x)
  intro raw T Q q φ M Used hUsed hmatch x
  have hh:=long_residual_surplus_degree_bound P S Small Del π d σ g j R a γ δ (2*θ*n+err) (ξ*n)
    hγ hCardU hDel h4 hedit M hUsed hmatch x
  linarith
end Oberwolfach
