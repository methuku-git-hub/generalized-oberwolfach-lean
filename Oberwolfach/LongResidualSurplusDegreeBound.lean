module

public import Oberwolfach.LongResidualSurplusPhysicalContainment
public import Oberwolfach.LongApproximateUnusedFromCommonIncidence

@[expose] public section
/-! The unmatched approximate-edge bound, unassigned-edge bound and actual
class edit bound control the whole class residual outside the reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_surplus_degree_bound
    {n:ℕ} {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (P S Small Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (g j:Bool) (R:C→Finset (LongRawHubResource n U)) (a γ δ δ₄ δedit:ℝ)
    (hγ:0≤γ) (hCardU:Fintype.card U≤n) (hDel:∀x,(Del.degree x:ℝ)≤δ)
    (h4:∀x,((longPhysicalStateGraph P σ {4}).degree x:ℝ)≤δ₄)
    (hEdit:∀x,((S\longPhysicalStateGraph P σ {0,1,2,3,4}).degree x:ℝ)≤δedit):
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
      δ₄+2*max a (4*γ)*n+δ+2*(6*d+2:ℕ)+δedit:=by
  intro raw T Q q φ M Used hUsed hmatch x
  let A:=longPhysicalStateGraph P σ {4}
  let B:=longPhysicalStateGraph P σ {2,3}\Used
  let Cbad:=longPreparationIneligibleGraph P π d
  let E:=S\longPhysicalStateGraph P σ {0,1,2,3,4}
  have hsub:=long_residual_surplus_physical_containment P S Used Small π d σ hUsed
  have hle:((((S\Small)\longSelectedPhysicalGraph P π d σ).degree x):ℝ)≤(((A⊔B)⊔Cbad)⊔E).degree x:=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub
  have h1:((((A⊔B)⊔Cbad)⊔E).degree x:ℝ)≤(((A⊔B)⊔Cbad).degree x:ℝ)+E.degree x:=by
    have hh:(((A⊔B)⊔Cbad)⊔E).degree x≤((A⊔B)⊔Cbad).degree x+E.degree x:=by
      convert graph_degree_sup_le ((A⊔B)⊔Cbad) E x using 1 <;> congr!
    exact_mod_cast hh
  have h2:(((A⊔B)⊔Cbad).degree x:ℝ)≤((A⊔B).degree x:ℝ)+Cbad.degree x:=by
    have hh:((A⊔B)⊔Cbad).degree x≤(A⊔B).degree x+Cbad.degree x:=by
      convert graph_degree_sup_le (A⊔B) Cbad x using 1 <;> congr!
    exact_mod_cast hh
  have h3:((A⊔B).degree x:ℝ)≤(A.degree x:ℝ)+B.degree x:=by
    have hh:(A⊔B).degree x≤A.degree x+B.degree x:=by
      convert graph_degree_sup_le A B x using 1 <;> congr!
    exact_mod_cast hh
  have hB:((B.degree x):ℝ)≤2*max a (4*γ)*n+δ+(6*d+2:ℕ):=by
    exact long_approximate_unused_degree_from_common_incidence P Del π d σ g j R a γ δ hγ hCardU hDel M hmatch x
  have hC:((Cbad.degree x):ℝ)≤(6*d+2:ℕ):=by
    exact_mod_cast long_preparation_ineligible_degree P π d x
  linarith [h4 x,hEdit x]
end Oberwolfach
