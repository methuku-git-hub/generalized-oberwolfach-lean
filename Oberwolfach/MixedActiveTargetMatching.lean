module

public import Oberwolfach.MixedSampledResourceLoads
public import Oberwolfach.MixedSampledResourceMatching

@[expose] public section
/-! Apply the proved weighted resource-matching theorem to the actual
restriction of a union of candidate families. Targets, candidate weights,
and the common sampled outcome are left unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_sampled_resource_matching_active_targets (r B:ℕ) (hr:2≤r) (hB:1≤B)
    (K a γ:ℝ) (hK:0<K) (ha:0<a) (hγ:0<γ):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n →
    ∀ (I V A J:Type) [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
      [Fintype A] [Fintype J]
      (E:I→Type) [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]
      (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (σ:V→Bool)
      (target:I→V→ℝ) (τ t:ℝ) (Kᵢ:I→ℝ),
    let W := {v:V // v∈bernoulliVertexSet σ}
    let e : W↪V := Function.Embedding.subtype _
    let C := RestrictedResource (mixedCandidateResources R) e
    let Q := restrictedResourceSet (mixedCandidateResources R) e
    ∀ (g:A→C→ℝ) (S:J→Finset W),
    Fintype.card W≤n^B → Fintype.card A≤n^B → Fintype.card J≤n^B →
    (∀i c,2≤(R i c).card ∧ (R i c).card≤r) → (∀i c,0≤w i c) →
    (∀v,v∈bernoulliVertexSet σ → ∑i,target i v=1) →
    (∀i v,v∈bernoulliVertexSet σ →
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ-target i v|≤t+τ*target i v) →
    (Fintype.card I:ℝ)*t+τ≤η₀ →
    (∀i u v,u≠v → resourceOmittedPairWeight (R i) (w i) u v≤Kᵢ i/n) →
    (∑i,Kᵢ i)≤K →
    (∀j,a*n≤(S j).card) → (∀i c,0≤g i c ∧ g i c≤1) →
    (∀i,a*n≤∑ c,g i c*mixedCandidateWeight w c.val) →
    ∃M:Finset C,(∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀j,((S j\M.biUnion Q).card:ℝ)≤γ*(S j).card) ∧
      (∀i,(1-γ)*(∑c,g i c*mixedCandidateWeight w c.val)≤∑c∈M,g i c) ∧
      (∀i,(∑c∈M,g i c)≤(1+γ)*(∑c,g i c*mixedCandidateWeight w c.val)) := by
  obtain ⟨η₀,hη,n₀,hmatch⟩ := fractional_resource_matching r B hr hB K a γ hK ha hγ
  refine ⟨η₀,hη,max n₀ 1,?_⟩
  intro n hn I V A J _ _ _ _ _ _ E _ _ R w σ target τ t Kᵢ
  dsimp only
  intro g S hW hA hJ hsize hw htarget hload herror hpair hKsum hS hg hmass
  have hn₀:n₀≤n := (le_max_left _ _).trans hn
  have hnpos:(0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  apply hmatch n hn₀ _ _ _ _ _ _ _ _ hW hA hJ
  · intro c
    rw [restrictedResourceSet_card]
    exact hsize c.val.1 c.val.2
  · intro c
    exact hw c.val.1 c.val.2
  · intro v
    have hh : |hypergraphWeightedDegree
      (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype _))
      (fun c=>mixedCandidateWeight w c.val) v-1|≤(Fintype.card I:ℝ)*t+τ := by
      rw [mixed_sampled_resource_degree_eq_sum]
      exact finite_combined_unit_load (fun i=>target i v.val)
        (fun i=>resourcePatternLoad (R i) (w i) (fun _ _=>true) v.val σ)
        τ t (htarget v.val v.property) (fun i=>hload i v.val v.property)
    have hl : -((Fintype.card I:ℝ)*t+τ)≤
      hypergraphWeightedDegree (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype _))
        (fun c=>mixedCandidateWeight w c.val) v-1 ∧
      hypergraphWeightedDegree (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype _))
        (fun c=>mixedCandidateWeight w c.val) v-1≤(Fintype.card I:ℝ)*t+τ := abs_le.mp hh
    constructor <;> linarith
  · intro u v huv
    have hh:=mixed_sampled_resource_codegree_bound R w σ Kᵢ n hw hpair u v huv
    exact hh.trans (div_le_div_of_nonneg_right hKsum (le_of_lt hnpos))
  · exact hS
  · exact hg
  · exact hmass
end Oberwolfach
