module

public import Oberwolfach.LongApproximateUnusedFromCommonIncidence

@[expose] public section
/-! The same surviving matching's incidence and deletion bounds supply the
approximate residual-degree budget after the order is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_approximate_residual_matching_margins
    (lam:ℝ) (hlam:0<lam) (d:ℕ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (g j:Bool) (R:C→Finset (LongRawHubResource n U)) (a γ δ:ℝ)
      (hγ:0≤γ) (hCardU:Fintype.card U≤n) (hDel:∀x,(Del.degree x:ℝ)≤δ)
      (hsmall:2*max a (4*γ)≤lam/3) (hδ:δ≤(lam/3)*n),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    (∀i,((longRawIncidenceSet S i\M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀x,((longPhysicalStateGraph P σ {2,3}\physicalRimCandidateUnion φ
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)).degree x:ℝ)≤lam*n:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (3*((6*d+2:ℕ):ℝ)/lam)
  refine ⟨N,?_⟩
  intro n hn U C _ _ _ _ P Del π σ g j R a γ δ hγ hCardU hDel hsmall hδ raw T S q φ M hmatch x
  have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
  have hlin:((6*d+2:ℕ):ℝ)≤(lam/3)*n:=by
    have hh:3*((6*d+2:ℕ):ℝ)/lam≤n:=(le_of_lt hN).trans hnR
    have hh':3*((6*d+2:ℕ):ℝ)≤(n:ℝ)*lam:=(div_le_iff₀ hlam).mp hh
    linarith
  have hsmall':2*max a (4*γ)*(n:ℝ)≤(lam/3)*n:=
    mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n)
  have hh:=long_approximate_unused_degree_from_common_incidence P Del π d σ g j R a γ δ hγ hCardU hDel M hmatch x
  linarith
end Oberwolfach
