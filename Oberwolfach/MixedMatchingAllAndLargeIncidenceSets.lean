module

public import Oberwolfach.MixedPositiveActiveMatching
public import Oberwolfach.MixedSampledResourceLoads
public import Oberwolfach.MixedSampledResourceMatching
public import Oberwolfach.PositiveFractionalResourceMatching

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

theorem mixed_sampled_resource_matching_all_and_large_incidence_sets (r B:ℕ) (hr:2≤r) (hB:1≤B)
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
    (∀i c,0<w i c → 2≤(R i c).card ∧ (R i c).card≤r) → (∀i c,0≤w i c) →
    (∀v,v∈bernoulliVertexSet σ → ∑i,target i v=1) →
    (∀i v,v∈bernoulliVertexSet σ →
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ-target i v|≤t+τ*target i v) →
    (Fintype.card I:ℝ)*t+τ≤η₀ →
    (∀i u v,u≠v → resourceOmittedPairWeight (R i) (w i) u v≤Kᵢ i/n) →
    (∑i,Kᵢ i)≤K →
    (∀i c,0≤g i c ∧ g i c≤1) →
    (∀i,a*n≤∑ c,g i c*mixedCandidateWeight w c.val) →
    ∃M:Finset C,(∀c∈M,0<mixedCandidateWeight w c.val) ∧
      (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀j,((S j\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(S j).card)) ∧
      (∀j,a*n≤(S j).card → ((S j\M.biUnion Q).card:ℝ)≤γ*(S j).card) ∧
      (∀i,(1-γ)*(∑c,g i c*mixedCandidateWeight w c.val)≤∑c∈M,g i c) ∧
      (∀i,(∑c∈M,g i c)≤(1+γ)*(∑c,g i c*mixedCandidateWeight w c.val)) :=by
  obtain ⟨η,hη,n₀,hmatch⟩:=mixed_sampled_resource_matching_positive_active_targets r B hr hB K a γ hK ha hγ
  refine ⟨η,hη,n₀,?_⟩
  intro n hn I V A J _ _ _ _ _ _ E _ _ R w σ target τ t Kᵢ W e C Q g S hW hA hJ hsize hw htarget hload herror hpair hsum hg hmass
  let Jlarge:Type:={j:J // a*n≤(S j).card}
  let Slarge:Jlarge→Finset W:=fun j=>S j.val
  have hJlarge:Fintype.card Jlarge≤n^B:=le_trans (Fintype.card_subtype_le _) hJ
  obtain ⟨M,hpos,hdis,hcov,hlow,hup⟩:=hmatch n hn I V A Jlarge E R w σ target τ t Kᵢ g Slarge
    hW hA hJlarge hsize hw htarget hload herror hpair hsum (fun j=>j.property) hg hmass
  refine ⟨M,hpos,hdis,?_,?_,hlow,hup⟩
  · intro j
    by_cases hj:a*n≤(S j).card
    · exact (hcov ⟨j,hj⟩).trans (le_max_right _ _)
    · have hc:((S j\M.biUnion Q).card:ℝ)≤(S j).card:=by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : S j\M.biUnion Q ⊆ S j)
      exact hc.trans ((le_of_not_ge hj).trans (le_max_left _ _))
  · intro j hj
    exact hcov ⟨j,hj⟩
end Oberwolfach
