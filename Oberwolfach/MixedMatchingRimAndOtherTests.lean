module

public import Oberwolfach.MixedMatchingAllAndLargeIncidenceSets
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! One matching gives the large physical-rim tests, all other incidence
tests, and the original fixed-weight tests simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_matching_rim_and_other_incidence_tests
    (r B:ℕ) (hr:2≤r) (hB:1≤B) (K a γ:ℝ) (hK:0<K) (ha:0<a) (hγ:0<γ):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n →
    ∀ (I V A X U J:Type) [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
      [Fintype A] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype J]
      (E:I→Type) [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]
      (R:∀i,E i→Finset V) (w:∀i,E i→ℝ) (σ:V→Bool)
      (target:I→V→ℝ) (τ t:ℝ) (Kᵢ:I→ℝ),
    let W:={v:V // v∈bernoulliVertexSet σ}
    let e:W↪V:=Function.Embedding.subtype _
    let C:=RestrictedResource (mixedCandidateResources R) e
    let Q:=restrictedResourceSet (mixedCandidateResources R) e
    ∀(g:A→C→ℝ) (φ:W↪Sym2 X⊕(X×U)) (S:J→Finset W),
    Fintype.card W≤n^B → Fintype.card A≤n^B → Fintype.card (X⊕J)≤n^B →
    (∀i c,0<w i c → 2≤(R i c).card ∧ (R i c).card≤r) → (∀i c,0≤w i c) →
    (∀v,v∈bernoulliVertexSet σ → ∑i,target i v=1) →
    (∀i v,v∈bernoulliVertexSet σ →
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ-target i v|≤t+τ*target i v) →
    (Fintype.card I:ℝ)*t+τ≤η₀ →
    (∀i u v,u≠v → resourceOmittedPairWeight (R i) (w i) u v≤Kᵢ i/n) →
    (∑i,Kᵢ i)≤K →
    (∀i c,0≤g i c ∧ g i c≤1) →
    (∀i,a*n≤∑c,g i c*mixedCandidateWeight w c.val) →
    ∃M:Finset C,(∀c∈M,0<mixedCandidateWeight w c.val) ∧
      (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀x,a*n≤(rimIncidentResources φ x).card →
        (((rimIncidentResources φ x\M.biUnion Q).card:ℕ):ℝ)≤γ*(rimIncidentResources φ x).card) ∧
      (∀j,((S j\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(S j).card)) ∧
      (∀j,a*n≤(S j).card → ((S j\M.biUnion Q).card:ℝ)≤γ*(S j).card) ∧
      (∀i,(1-γ)*(∑c,g i c*mixedCandidateWeight w c.val)≤∑c∈M,g i c) ∧
      (∀i,(∑c∈M,g i c)≤(1+γ)*(∑c,g i c*mixedCandidateWeight w c.val)) :=by
  obtain ⟨η,hη,n₀,hmatch⟩:=mixed_sampled_resource_matching_all_and_large_incidence_sets r B hr hB K a γ hK ha hγ
  refine ⟨η,hη,n₀,?_⟩
  intro n hn I V A X U J _ _ _ _ _ _ _ _ _ _ E _ _ R w σ target τ t Kᵢ W e C Q g φ S hW hA hJ hsize hw htarget hload herror hpair hsum hg hmass
  let S':X⊕J→Finset W:=Sum.elim (rimIncidentResources φ) S
  obtain ⟨M,hpos,hdis,hall,hlarge,hlow,hup⟩:=hmatch n hn I V A (X⊕J) E R w σ target τ t Kᵢ g S'
    hW hA hJ hsize hw htarget hload herror hpair hsum hg hmass
  refine ⟨M,hpos,hdis,?_,?_,?_,hlow,hup⟩
  · intro x hx
    exact hlarge (Sum.inl x) hx
  · intro j
    exact hall (Sum.inr j)
  · intro j hj
    exact hlarge (Sum.inr j) hj
end Oberwolfach
