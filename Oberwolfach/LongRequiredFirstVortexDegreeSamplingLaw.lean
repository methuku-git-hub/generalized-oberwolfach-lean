module

public import Oberwolfach.LongRequiredFirstVortexDegreeFromPositiveCommon
public import Oberwolfach.LongUnassignedDensityBounds
public import Oberwolfach.FirstVortexHubCardinality
public import Oberwolfach.FirstVortexDeletionRateMargin
public import Oberwolfach.FirstVortexMatchingIncidenceMargin

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_required_first_vortex_degree_local_from_sampling_law
    (α lam ε θ δlocal:ℝ) (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδlocal:0<δlocal)
    (hθlocal:θ≤δlocal/32) (hlamlocal:lam≤δlocal*ε/32) (d K mPath:ℕ) (eps ξ:ℝ)
    (hd:3≤d) (hK:1≤K) (hmPath:1≤mPath) (hθ:0≤θ) (hθhi:θ≤1/100)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P P₀ Sel Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β:ℝ)
      (Q:Vortex U P Dv β ε m) (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv)
      (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (hρhi:initialIndexDensity U Dv≤1) (π:Equiv.Perm (Fin n)) (D M:Fin n→Fin n→Prop)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (g j:Bool) (R:C→Finset (LongRawHubResource n U)),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀matchSet:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (matchSet.map q)
    let I:=Q.extendedVertices 1
    P₀≤longPhysicalStateGraph P σ {0,1,2,3,4}\Used→
    (∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y)→
    let u:=2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/(mPath:ℝ)-
      longAssignedApproxMarkedWeight F hF K mPath θ w-longAssignedApproxOrdinaryWeight F hF K mPath θ w))/(Dv:ℝ)
    ∀ (C₀ a γ δ:ℝ),1≤C₀→ε≤α/(1000*C₀)→lam≤α/128→0≤γ→
    a≤lam/(10*d)→γ≤lam/(10*d)→
    (∀x,(Del.degree x:ℝ)≤δ)→δ≤ξ*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    0<m→
    ∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤δlocal*I.card/4 :=by
  have hd1:1≤d:=by omega
  obtain ⟨N,hN⟩:=long_required_first_vortex_degree_local_from_common_positive_vortex α lam ε θ δlocal hα hlam hε hδlocal hθlocal hlamlocal d hd1
  refine ⟨max N 1,?_⟩
  intro n hn U C _ _ _ _ P P₀ Sel Del Dv m β Q hreg hDv F hF hρhi π D M σ g j R raw T S f q φ matchSet Used I hP₀ hSel u C₀ a γ δ hC hehi hlamhi hγ ha hγrate hDel hδ hrow hmatch hm
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hn0:0<n:=by omega
  have hθ1:θ≤1:=by linarith only [hθhi]
  have hu:=long_unassigned_density_bounds (by omega : 0<n) hK hmPath hDv F hF θ hθ hθ1 hρhi
  have hCardU:=first_vortex_hub_cardinality_le_host hreg hn0 hDv hρhi
  have hmax:=first_vortex_matching_incidence_margin d lam a γ hd hlam.le ha hγrate
  have hξlam:=first_vortex_deletion_rate_margin K θ lam eps ξ hK hθ hθ1 hlam.le heps hξ
  have hδ':δ≤(lam/3)*n:=le_trans hδ (mul_le_mul_of_nonneg_right hξlam (Nat.cast_nonneg n))
  exact hN n hnN U C P P₀ Sel Del Dv m β Q π D M σ g j R matchSet hP₀ hSel C₀ u a γ δ hθ hθhi hε.le hC hehi hlamhi hu.1 hu.2 hγ hCardU hmax hDel hδ' hrow hmatch hm
end Oberwolfach
