module

public import Oberwolfach.LongRequiredExtendedHost
public import Oberwolfach.LongRequiredRowsFromCommonIncidence
public import Oberwolfach.LongApproximateUnusedFromCommonIncidence
public import Oberwolfach.LongApproximateResidualAfterDeletion
public import Oberwolfach.LongRequiredVortexRowMargins

@[expose] public section
/-! The existing first-vortex required-graph bounds from a matching selected
after a later physical rim deletion, with its realised degree loss retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_required_graph_from_common_incidence
    (α lam:ℝ) (hα:0<α) (hlam:0<lam) (d:ℕ) (hd:1≤d):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β ε:ℝ)
      (Q:Vortex U P Dv β ε m) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop)
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
    let P₀:=longPhysicalStateGraph P σ {0,1,2,3,4}\Used
    let Sel:=longSelectedPhysicalGraph P π d σ
    let M:=fun x y=>Used.Adj x y

    ∀ (θ C₀ u a γ δ:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→0≤γ→Fintype.card U≤n→2*max a (4*γ)≤lam/3→
    (∀x,(Del.degree x:ℝ)≤δ)→δ≤(lam/3)*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀Pack:Finset (Sym2 (Fin n)),Pack⊆Used.edgeFinset→
    (∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤(α/16)*n) ∧
    ((longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset.card:ℝ)≤
      (θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n ∧
    Disjoint (longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset Pack :=by
  obtain ⟨N,hN⟩:=long_required_vortex_rows_from_common_incidence α lam hα hlam d hd
  refine ⟨N,?_⟩
  intro n hn U C _ _ _ _ P Del Dv m β ε Q π D σ g j R raw T S f q φ matchSet Used I P₀ Sel M θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch Pack hPack
  have hSel:∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y:=by
    intro x hx y hy h
    exact h
  obtain ⟨hdegree,hedges⟩:=hN n hn U C P P₀ Sel Del Dv m β ε Q π D M σ g j R matchSet
    le_rfl hSel θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch
  have hP₀:P₀≤P\Used:=by
    intro x y h
    exact ⟨h.1.1,h.2⟩
  have hdis:=long_required_graph_avoids_used_packing P P₀ Sel Used π d I D Pack hP₀ hPack
  exact ⟨hdegree,hedges,hdis⟩
end Oberwolfach
