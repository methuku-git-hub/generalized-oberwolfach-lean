module

public import Oberwolfach.LongApproximateSampleGraphEmbedding
public import Oberwolfach.PhysicalRimResourceResidual
public import Oberwolfach.LongPreparationBadGraphBounds

@[expose] public section
/-! Actual unused approximate physical edges lie in the uncovered sampled
rim graph or the explicitly bounded ineligible graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_approximate_unused_resource_containment
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g:Γ) (j:Color):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀covered:Finset {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g j))},
    longPhysicalStateGraph P σ {2,3}\physicalRimCoveredGraph φ covered ≤
      physicalRimResidualGraph φ covered ⊔ longPreparationIneligibleGraph P π d := by
  intro raw φ covered x y h
  have hP:P.Adj x y:=h.1.1
  have hnot:¬(physicalRimCoveredGraph φ covered).Adj x y:=h.2
  by_cases hbad:(longPreparationIneligibleGraph P π d).Adj x y
  · exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inr hbad)
  · have hstate:(σ (Sum.inl s(x,y))).1=2 ∨ (σ (Sum.inl s(x,y))).1=3 := by
      simpa [longPhysicalStateGraph] using h.1.2
    have hap:=approximate_state_outside_ineligible_is_sampled P π d σ x y hP hbad hstate
    obtain ⟨w,hw⟩:=long_approximate_edge_has_raw_resource P π d σ g j x y hap
    have hw':w∉covered:=by
      intro hc
      apply hnot
      exact ⟨hP.ne,w,hc,hw⟩
    exact (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl ⟨hP.ne,w,hw',hw⟩)
/-- A matching need only test sufficiently large sets of incident rim
resources; the discarded permutation-close pairs are counted separately. -/
theorem long_approximate_unused_degree_from_coverage
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g:Γ) (j:Color) (a γ:ℝ) (hγ:0≤γ):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀covered:Finset {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw g j))},
    (∀x,a*(Fintype.card V:ℝ)≤(rimIncidentResources φ x).card →
      (((rimIncidentResources φ x\covered).card:ℕ):ℝ)≤γ*(rimIncidentResources φ x).card) →
    ∀x,((longPhysicalStateGraph P σ {2,3}\physicalRimCoveredGraph φ covered).degree x:ℝ)
      ≤ max a γ*(Fintype.card V:ℝ)+(6*d+2:ℕ) := by
  intro raw φ covered hlarge x
  let R:=physicalRimResidualGraph φ covered
  let F:=longPreparationIneligibleGraph P π d
  have hs:=long_approximate_unused_resource_containment P π d σ g j covered
  have hm:((longPhysicalStateGraph P σ {2,3}\physicalRimCoveredGraph φ covered).degree x:ℝ)≤((R⊔F).degree x:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hs
  have hu:(((R⊔F).degree x):ℝ)≤(R.degree x:ℝ)+F.degree x:=by
    exact_mod_cast graph_degree_sup_le R F x
  have hr:((R.degree x):ℝ)≤max a γ*(Fintype.card V:ℝ):=
    physical_rim_residual_degree_from_large_coverage φ covered a γ hγ hlarge x
  have hf:((F.degree x):ℝ)≤(6*d+2:ℕ):=by
    exact_mod_cast long_preparation_ineligible_degree P π d x
  linarith
/-- Formulation for the physical rim graph of the selected candidate family. -/
theorem long_approximate_unused_degree_from_matching
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (g:Γ) (j:Color) (a γ:ℝ) (hγ:0≤γ):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀ (C:Type) [Fintype C] [DecidableEq C]
      (R:C→Finset {z // z∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
        (rawMarkedPairSpokes π d raw g j))}) (M:Finset C),
    (∀x,a*(Fintype.card V:ℝ)≤(rimIncidentResources φ x).card →
      (((rimIncidentResources φ x\M.biUnion R).card:ℕ):ℝ)≤γ*(rimIncidentResources φ x).card) →
    ∀x,((longPhysicalStateGraph P σ {2,3}\physicalRimCandidateUnion φ R M).degree x:ℝ)
      ≤ max a γ*(Fintype.card V:ℝ)+(6*d+2:ℕ) := by
  intro raw φ C _ _ R M hlarge x
  rw [←physical_rim_covered_eq_candidate_union φ R M]
  exact long_approximate_unused_degree_from_coverage P π d σ g j a γ hγ (M.biUnion R) hlarge x
end Oberwolfach
