module

public import Oberwolfach.FirstVortexAllHubCapacityDegreeInputs
public import Oberwolfach.LongRequiredPreciseFromCommonIncidence

@[expose] public section
/-! The common matching and the chosen class correction supply the precise
degree hypotheses used by both protected and all-hub target capacity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_capacity_inputs_from_common_matching
    (α lam ε θ ξ ageom δglobal:ℝ) (d:ℕ)
    (hα:0<α) (hlam:0<lam) (hd:1≤d) (hε:0≤ε) (hθ:0<θ) (hθmax:θ≤1/100)
    (hageom:0<ageom) (hageom1:ageom≤1) (hεsmall:ε≤ageom/8192)
    (hsmall:lam+ξ≤ageom*θ/4096) (hglobal:10*θ≤δglobal):
    ∃N:ℕ,∀n:ℕ,N≤n→
    ∀(U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P Sclass Sel Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β:ℝ)
      (Q:Vortex U P Dv β ε m) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (g j:Bool) (R:C→Finset (LongRawHubResource n U)),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let hST:=long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset
    let q:=survivingCandidateEmbedding R S T hST
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀matchSet:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (matchSet.map q)
    let I:=Q.extendedVertices 1
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4}
    Sclass≤P→
    (∀v,((changed (S₀.neighborFinset v) (Sclass.neighborFinset v)).card:ℝ)≤ξ*n)→
    (∀x∈I,∀y∈I,(longSelectedPhysicalGraph P π d σ).Adj x y→Sel.Adj x y)→
    ∀(C₀ u a γ δDel:ℝ),1≤C₀→ε≤α/(1000*C₀)→lam≤α/128→
    0≤u→u≤2*θ→0≤γ→Fintype.card U≤n→2*max a (4*γ)≤lam/3→
    (∀x,(Del.degree x:ℝ)≤δDel)→δDel≤(lam/3)*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop,
    (∀Old Pack,Extra Old Pack→Pack=Used.edgeFinset)→
    let Kbase:=longRequiredPhysicalGraph Sclass (Sclass\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack=>longClassInnerRequiredRepair Sclass Used Kbase I Pack;
    (∀Old Pack,Extra Old Pack→∀v,((Kplus Pack).degree v:ℝ)≤((ageom*θ/64)/16)*n) ∧
    (∀Old Pack,Extra Old Pack→∀v,((Kplus Pack).degree v:ℝ)≤δglobal*n/4) :=by
  obtain ⟨N₁,hN₁⟩:=long_required_vortex_rows_precise_from_common_incidence α lam hα hlam d hd
  obtain ⟨N₂,hN₂⟩:=first_vortex_all_hub_capacity_degree_inputs ε θ lam ξ ageom δglobal d hε hθ hageom hageom1 hεsmall hsmall hglobal
  refine ⟨max N₁ N₂,?_⟩
  intro n hn U C _ _ _ _ P Sclass Sel Del Dv m β Q π D σ g j R raw T S hST q φ matchSet Used I S₀ hSP hedit hSel C₀ u a γ δDel hC hehi hlamhi hu huhi hγ hU hmax hDel hδ hrow hmatch Extra hpack Kbase Kplus
  have hh:=hN₁ n (by omega) U C P (S₀\Used) Sel Del Dv m β ε Q π D (fun x y=>Used.Adj x y) σ g j R matchSet
    (by dsimp only [S₀];exact le_rfl) hSel θ C₀ u a γ δDel hθ.le hθmax hε hC hehi hlamhi hu huhi hγ hU hmax hDel hδ hrow hmatch
  have hp:=hh.2.2
  exact hN₂ n (by omega) Q π D hSP hedit hp Extra hpack
end Oberwolfach
