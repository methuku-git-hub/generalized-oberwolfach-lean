module

public import Oberwolfach.FirstVortexNonempty
public import Oberwolfach.FirstVortexRequiredDegreeLocalBound
public import Oberwolfach.LongRequiredPreciseFromCommonIncidence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_required_first_vortex_degree_local_from_common_positive_vortex
    (α lam ε θ δlocal:ℝ) (hα:0<α) (hlam:0<lam) (hε:0<ε) (hδlocal:0<δlocal)
    (hθlocal:θ≤δlocal/32) (hlamlocal:lam≤δlocal*ε/32) (d:ℕ) (hd:1≤d):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P P₀ Sel Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β:ℝ)
      (Q:Vortex U P Dv β ε m) (π:Equiv.Perm (Fin n)) (D M:Fin n→Fin n→Prop)
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
    ∀ (C₀ u a γ δ:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→0≤γ→Fintype.card U≤n→2*max a (4*γ)≤lam/3→
    (∀x,(Del.degree x:ℝ)≤δ)→δ≤(lam/3)*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    0<m→
    ∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤δlocal*I.card/4 :=by
  obtain ⟨N₁,hN₁⟩:=long_required_vortex_rows_precise_from_common_incidence α lam hα hlam d hd
  obtain ⟨N₂,hN₂⟩:=first_vortex_required_degree_local_bound ε δlocal θ lam d hε hδlocal hθlocal hlamlocal
  refine ⟨max N₁ N₂,?_⟩
  intro n hn U C _ _ _ _ P P₀ Sel Del Dv m β Q π D M σ g j R raw T S f q φ matchSet Used I hP₀ hSel C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch hm
  have hN1:N₁≤n:=le_trans (le_max_left _ _) hn
  have hN2:N₂≤n:=le_trans (le_max_right _ _) hn
  have hh:=hN₁ n hN1 U C P P₀ Sel Del Dv m β ε Q π D M σ g j R matchSet hP₀ hSel
    θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch
  have hIpos:1≤I.card:=Q.first_inner_vertex_nonempty hε hm
  apply hN₂ n hN2 Q hIpos ?_
  intro v
  convert hh.2.2 v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
