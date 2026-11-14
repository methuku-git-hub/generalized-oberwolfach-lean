module

public import Oberwolfach.MixedMatchingRimNamedState
public import Oberwolfach.LongRawIncidenceFamily
public import Oberwolfach.LongRawSeedResourceSizes
public import Oberwolfach.LongRawDeletedStateBool
public import Oberwolfach.LongRawMatchingResidualAfterDeletion

@[expose] public section
/-! Apply one weighted matching to the actual surviving long raw candidate
family. Physical rims, auxiliary endpoint incidences, typed spokes, and all
supplied fixed-weight tests refer to this same matching and original outcome.
The load, pair-weight and weighted-test mass estimates remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_raw_surviving_matching_all_incidences
    (m K:ℕ) (ℓ:Fin K→ℕ) (hℓ:∀i,1≤ℓ i) (hℓmax:∀i,ℓ i≤K)
    (Kpair a γ:ℝ) (hKpair:0<Kpair) (ha:0<a) (hγ:0<γ):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n →
    ∀(U A:Type) [Fintype U] [DecidableEq U] [Fintype A],
    Fintype.card U≤n →
    ∀(P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
      (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
      (w:∀i,longRawHubCandidates (U:=U) π d m ℓ i→ℝ)
      (target:Option (Fin K)→LongRawHubResource n U→ℝ) (τ t:ℝ) (Kᵢ:Option (Fin K)→ℝ),
    let R:=longRawHubResources (U:=U) π d m ℓ
    let state:=longRawHubState P π d (rawMarkedDeleteRims raw Del.edgeFinset) g j
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
    let C:=RestrictedResource (mixedCandidateResources R) e
    let Q:=restrictedResourceSet (mixedCandidateResources R) e
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=f.trans (markedRawSampledPhysicalEmbedding P π d raw g j)
    ∀test:A→C→ℝ,
    Fintype.card A≤n^3 →
    (∀i c,0≤w i c) →
    (∀v,v∈bernoulliVertexSet state → ∑i,target i v=1) →
    (∀i v,v∈bernoulliVertexSet state →
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v state-target i v|≤t+τ*target i v) →
    (Fintype.card (Option (Fin K)):ℝ)*t+τ≤η₀ →
    (∀i u v,u≠v → resourceOmittedPairWeight (R i) (w i) u v≤Kᵢ i/n) →
    (∑i,Kᵢ i)≤Kpair →
    (∀i c,0≤test i c ∧ test i c≤1) →
    (∀i,a*n≤∑c,test i c*mixedCandidateWeight w c.val) →
    ∃M:Finset C,(∀c∈M,0<mixedCandidateWeight w c.val) ∧
      (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀x,a*n≤(rimIncidentResources φ x).card →
        ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
      (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤
        max (a*n) (γ*(longRawIncidenceSet S i).card)) ∧
      (∀i,a*n≤(longRawIncidenceSet S i).card →
        ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
      (∀i,(1-γ)*(∑c,test i c*mixedCandidateWeight w c.val)≤∑c∈M,test i c) ∧
      (∀i,(∑c∈M,test i c)≤(1+γ)*(∑c,test i c*mixedCandidateWeight w c.val)) ∧
      (∀δ:ℝ,(∀x,(Del.degree x:ℝ)≤δ) →
        let lift:=survivingCandidateEmbedding (mixedCandidateResources R) S T
          (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
        ∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw g j)
          ((M.map lift).biUnion (restrictedResourceSet (mixedCandidateResources R)
            (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max a γ*n+δ) :=by
  have hr:2≤2*max (m+1) K:=by omega
  obtain ⟨η,hη,n₀,hmatch⟩:=mixed_matching_rim_and_other_incidence_tests_on_named_state
    (2*max (m+1) K) 3 hr (by omega) Kpair a γ hKpair ha hγ
  refine ⟨η,hη,max n₀ 4,?_⟩
  intro n hn U A _ _ _ hu P Del π d raw g j w target τ t Kᵢ R state T S e C Q f φ test hA hw htarget hload herr hpair hsum htest hmass
  have hn₀:n₀≤n:=(le_max_left _ _).trans hn
  have hn4:4≤n:=(le_max_right _ _).trans hn
  have hstate:bernoulliVertexSet state=S:=
    (long_raw_surviving_state_is_raw_rim_deletion P π d raw g j Del.edgeFinset).symm
  obtain ⟨M,hpos,hdis,hrim,hall,hlarge,hlow,hup⟩:=hmatch n hn₀ (Option (Fin K)) (LongRawHubResource n U) A (Fin n) U
    (LongRawIncidenceIndex n U) (longRawHubCandidates (U:=U) π d m ℓ)
    R w state S hstate target τ t Kᵢ test φ (longRawIncidenceSet S)
    (long_raw_surviving_resource_card_le_cube hn4 hu S) hA
    (long_raw_incidence_test_index_card_le_cube n hn4 U hu)
    (fun i c _=>long_raw_seed_resource_sizes π d m ℓ hℓ hℓmax i c)
    hw htarget hload herr hpair hsum htest (by
      intro i
      convert hmass i using 1 <;> congr 3 <;> exact Subsingleton.elim _ _)
  refine ⟨M,hpos,hdis,hrim,hall,hlarge,?_,?_,?_⟩
  · intro i
    convert hlow i using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  · intro i
    convert hup i using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  · intro δ hDel lift x
    exact long_raw_matching_residual_degree_after_rim_deletion P Del π d raw g j
      (mixedCandidateResources R) a γ δ hγ.le hDel M hrim x
end Oberwolfach
