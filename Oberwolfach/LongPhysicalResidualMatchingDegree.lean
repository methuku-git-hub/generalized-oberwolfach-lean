module

public import Oberwolfach.LongPhysicalIncidenceMatchingBound

@[expose] public section
/-! The same matching's uncovered rim-incidence tests bound the degree of the
remaining surviving approximate physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_physical_residual_matching_degree
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j;
    ∀(covered:Finset S) (a γ:ℝ),0≤γ→Fintype.card U≤n→
      (∀i,((longRawIncidenceSet S i\covered).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))→
      ∀x,((physicalRimResidualGraph (f.trans φ) covered).degree x:ℝ)≤2*max a (4*γ)*n:=by
  intro T S f φ covered a γ hγ hu hmatch x
  have hcount:=long_physical_rim_incidence_from_matching_bounds P Del π d raw g j covered a γ hγ hu hmatch x
  have hdeg:((physicalRimResidualGraph (f.trans φ) covered).degree x:ℝ)≤
      ((rimIncidentResources (f.trans φ) x\covered).card:ℝ):=by
    exact_mod_cast physical_rim_residual_degree_le_uncovered (f.trans φ) covered x
  exact hdeg.trans hcount
end Oberwolfach
