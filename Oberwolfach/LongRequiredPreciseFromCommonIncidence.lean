module

public import Oberwolfach.LongRequiredDegreePreciseFromRows
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

theorem long_required_vortex_rows_precise_from_common_incidence
    (α lam:ℝ) (hα:0<α) (hlam:0<lam) (d:ℕ) (hd:1≤d):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P P₀ Sel Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β ε:ℝ)
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
    ∀ (θ C₀ u a γ δ:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→0≤γ→Fintype.card U≤n→2*max a (4*γ)≤lam/3→
    (∀x,(Del.degree x:ℝ)≤δ)→δ≤(lam/3)*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    (∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤(α/16)*n) ∧
    ((longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset.card:ℝ)≤
      (θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n ∧
    ∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤
      2*θ*I.card+(n:ℝ)^(3/4:ℝ)+lam*n+(6*d+2:ℕ) :=by
  obtain ⟨N₁,hN₁⟩:=long_required_vortex_row_margins α lam hα hlam d hd
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt (3*((6*d+2:ℕ):ℝ)/lam)
  refine ⟨max N₁ N₂,?_⟩
  intro n hn U C _ _ _ _ P P₀ Sel Del Dv m β ε Q π D M σ g j R raw T S f q φ matchSet Used I hP₀ hSel θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch
  have hN1:N₁≤n:=le_trans (le_max_left _ _) hn
  have hN2:N₂≤n:=le_trans (le_max_right _ _) hn
  have hN2r:(N₂:ℝ)≤n:=by exact_mod_cast hN2
  have hlin:((6*d+2:ℕ):ℝ)≤(lam/3)*(n:ℝ):=by
    have hh:3*((6*d+2:ℕ):ℝ)/lam≤n:=le_trans (le_of_lt hN₂) hN2r
    have hh':3*((6*d+2:ℕ):ℝ)≤(n:ℝ)*lam:=(div_le_iff₀ hlam).mp hh
    linarith
  have hsmall:2*max a (4*γ)*(n:ℝ)≤(lam/3)*(n:ℝ):=by
    nlinarith [mul_le_mul_of_nonneg_right hmax (Nat.cast_nonneg n)]
  have hB:∀v∈I,((longPhysicalStateGraph P σ {2,3}\Used).degree v:ℝ)≤lam*n:=by
    intro v hv
    have hh:=long_approximate_unused_degree_from_common_incidence P Del π d σ g j R a γ δ hγ hCardU hDel matchSet hmatch v
    dsimp only [Used] at *
    linarith
  have hold:= hN₁ (Fin n) U Bool Bool P P₀ Sel Used Dv m β ε Q (by simpa using hN1)
    π D M σ hP₀ hSel θ C₀ u hθ hθhi he hC hehi hlamhi hu huhi
    (by
      intro v hv
      convert hrow v hv using 1 <;> congr! 6 <;> first | exact Fintype.card_fin _ | (congr 1; exact Subsingleton.elim _ _) | exact Subsingleton.elim _ _)
    (by
      intro v hv
      convert hB v hv using 1 <;> congr! 6 <;> exact Fintype.card_fin _)
  have hp:=long_required_degree_precise_from_fixed_inner_rows P P₀ Sel Used π d I D M σ hP₀ hSel
    θ lam ((n:ℝ)^(3/4:ℝ)) u hθ hlam.le (by positivity) hu huhi
    (by intro v hv; convert (hrow v hv).le using 1 <;> congr! 6 <;> first | exact Fintype.card_fin _ | (congr 1; exact Subsingleton.elim _ _) | exact Subsingleton.elim _ _)
    (by intro v hv; convert hB v hv using 1 <;> congr! 6 <;> exact Fintype.card_fin _)
  refine ⟨?_,?_,?_⟩
  · simpa only [Fintype.card_fin] using hold.1
  · simpa only [Fintype.card_fin] using hold.2
  · simpa only [Fintype.card_fin] using hp
end Oberwolfach
