module

public import Oberwolfach.LongRawMatchingAllIncidences
public import Oberwolfach.LongRetainedHubTestsFromTargets

@[expose] public section
/-! One matching for the actual retained length-and-hub tests and all raw
incidences. The matching tolerance and order threshold precede the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_raw_matching_retained_hub_and_incidence_tests
    (m K:ℕ) (ℓ:Fin K→ℕ) (hℓ:∀i,1≤ℓ i) (hℓmax:∀i,ℓ i≤K)
    (Kpair a γ:ℝ) (hKpair:0<Kpair) (ha:0<a) (hγ:0<γ):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n →
    ∀(U:Type) [Fintype U] [DecidableEq U], Fintype.card U≤n →
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ)
      (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
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
    let hub:=longRawHubNames (U:=U) π d m ℓ
    let test:=fun (z:LongRetainedHubTest F hF K θ) (c:C)=>longRetainedHubIndicator F hF θ hub z c.val
    (∀i c,0≤w i c) →
    (∀v,v∈bernoulliVertexSet state → ∑i,target i v=1) →
    (∀i v,v∈bernoulliVertexSet state →
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v state-target i v|≤t+τ*target i v) →
    (Fintype.card (Option (Fin K)):ℝ)*t+τ≤η₀ →
    (∀i u v,u≠v → resourceOmittedPairWeight (R i) (w i) u v≤Kᵢ i/n) →
    (∑i,Kᵢ i)≤Kpair →
    (∀z,a*n≤∑c,test z c*mixedCandidateWeight w c.val) →
    ∃M:Finset C,(∀c∈M,0<mixedCandidateWeight w c.val) ∧
      (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀x,a*n≤(rimIncidentResources φ x).card →
        ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
      (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤
        max (a*n) (γ*(longRawIncidenceSet S i).card)) ∧
      (∀i,a*n≤(longRawIncidenceSet S i).card →
        ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
      (∀z,(1-γ)*(∑c,test z c*mixedCandidateWeight w c.val)≤∑c∈M,test z c) ∧
      (∀z,(∑c∈M,test z c)≤(1+γ)*(∑c,test z c*mixedCandidateWeight w c.val)) ∧
      (∀δ:ℝ,(∀x,(Del.degree x:ℝ)≤δ) →
        let lift:=survivingCandidateEmbedding (mixedCandidateResources R) S T
          (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
        ∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw g j)
          ((M.map lift).biUnion (restrictedResourceSet (mixedCandidateResources R)
            (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max a γ*n+δ) :=by
  obtain ⟨η,hη,n₀,hmatch⟩:=long_raw_surviving_matching_all_incidences m K ℓ hℓ hℓmax Kpair a γ hKpair ha hγ
  refine ⟨η,hη,max (max n₀ K) 1,?_⟩
  intro n hn U _ _ hu F hF θ P Del π d raw g j w target τ t Kᵢ R state T S e C Q f φ hub test hw htarget hload herr hpair hsum hmass
  have hn₀:n₀≤n:=(le_trans (le_max_left _ _) (le_max_left _ _)).trans hn
  have hKn:K≤n:=(le_trans (le_max_right _ _) (le_max_left _ _)).trans hn
  have hn1:1≤n:=(le_max_right _ _).trans hn
  have htestCard:Fintype.card (LongRetainedHubTest F hF K θ)≤n^3:=by
    have h:=long_retained_hub_tests_card_bound F hF K θ hu hKn
    have hn2:n^2≤n^3:=by nlinarith
    exact h.trans hn2
  have htest:∀z c,0≤test z c ∧ test z c≤1:=by
    intro z c
    exact long_retained_hub_indicator_range F hF θ hub z c.val
  exact hmatch n hn₀ U (LongRetainedHubTest F hF K θ) hu P Del π d raw g j w target τ t Kᵢ test htestCard hw htarget hload herr hpair hsum htest hmass
end Oberwolfach
