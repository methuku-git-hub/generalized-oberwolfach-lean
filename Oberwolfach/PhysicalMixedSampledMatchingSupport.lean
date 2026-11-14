module

public import Oberwolfach.PhysicalMixedSampledDegreeTargets
public import Oberwolfach.PhysicalResourcePairFiberBound
public import Oberwolfach.FractionalResourceMatchingSupport

@[expose] public section
/-! Weighted matching of a mixed family on physical resources, from its
common-sample typed root tests and typed pair bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physical_mixed_sampled_matching_support (r Bpow:ℕ) (hr:2≤r) (hB:1≤Bpow)
    (K α γ:ℝ) (hK:0<K) (hα:0<α) (hγ:0<γ):
    ∃ε:ℝ,0<ε ∧ ∃n₀:ℕ,∀n:ℕ,n₀≤n→
    ∀(I A V Test Row:Type) [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A]
      [Fintype V] [DecidableEq V] [Fintype Test] [Fintype Row],
    ∀(E:I→Type) [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]
      (φ:A→V) (R:∀i,E i→Finset A) (w:∀i,E i→ℝ) (σ:A→Bool)
      (M:ℕ) (target:I→A→ℝ) (τ t:ℝ) (Ki:I→ℝ),
    let W:=PhysicalSampledActive φ σ
    let Cand:=PhysicalSampledCandidate (mixedCandidateResources R) σ
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources R) σ;
    ∀(g:Test→Cand→ℝ) (S:Row→Finset W),
    Fintype.card W≤n^Bpow→Fintype.card Test≤n^Bpow→Fintype.card Row≤n^Bpow→
    (∀i c,Set.InjOn φ (↑(R i c):Set A))→(∀i c,2≤(R i c).card ∧ (R i c).card≤r)→
    (∀i c,0≤w i c)→(∀x,(Finset.univ.filter (fun a=>φ a=x)).card≤M)→
    0≤t→(M:ℝ)*(Fintype.card I:ℝ)*t+τ≤ε→
    (∀x:W,∑a∈Finset.univ.filter (fun a=>φ a=x.val ∧ σ a=true),∑i,target i a=1)→
    (∀i a,σ a=true→|resourcePatternLoad (R i) (w i) (fun _ _=>true) a σ-target i a|≤t+τ*target i a)→
    (∀i,0≤Ki i)→(∀i a b,resourceOmittedPairWeight (R i) (w i) a b≤Ki i/n)→
    (∑i,(M:ℝ)^2*Ki i)≤K→
    (∀j,α*n≤(S j).card)→(∀i c,0≤g i c ∧ g i c≤1)→
    (∀i,α*n≤∑c:Cand,g i c*mixedCandidateWeight w c.val)→
    ∃L:Finset Cand,(∀c∈L,0<mixedCandidateWeight w c.val) ∧ (∀c∈L,∀c'∈L,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀j,((S j\L.biUnion Q).card:ℝ)≤γ*(S j).card) ∧
      (∀i,(1-γ)*(∑c:Cand,g i c*mixedCandidateWeight w c.val)≤∑c∈L,g i c) ∧
      (∀i,(∑c∈L,g i c)≤(1+γ)*(∑c:Cand,g i c*mixedCandidateWeight w c.val)) :=by
  obtain ⟨ε,hε,n₀,hmatch⟩:=fractional_resource_matching_support r Bpow hr hB K α γ hK hα hγ
  refine ⟨ε,hε,max n₀ 1,?_⟩
  intro n hn I A V Test Row _ _ _ _ _ _ _ _ E _ _ φ R w σ M target τ t Ki
  dsimp only
  intro g S hW hTest hRow hinj hsize hw hM ht herr htarget hload hKi hpair hKsum hS hg hmass
  have hn0:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  let Rphys:=fun i c=>(R i c).image φ
  have hpairs:∀i x y,x≠y→(∑c,if x∈Rphys i c ∧ y∈Rphys i c then w i c else 0)≤
      ((M:ℝ)^2*Ki i)/n:=by
    intro i x y hxy
    have hh:=physical_resource_pair_weight_bounded_fibers φ (R i) (w i) (hw i) M hM
      (Ki i/n) (div_nonneg (hKi i) hn0.le) (hpair i) x y hxy
    convert hh using 1 <;> ring
  have hfull:=mixed_candidate_codegree_from_components Rphys w (fun i=>(M:ℝ)^2*Ki i) n hpairs
  apply hmatch n ((le_max_left _ _).trans hn) (PhysicalSampledActive φ σ)
    (PhysicalSampledCandidate (mixedCandidateResources R) σ) Test Row
    (physicalSampledCandidateSet φ (mixedCandidateResources R) σ) (fun c=>mixedCandidateWeight w c.val)
    g S hW hTest hRow
  · intro c
    rw [physical_sampled_candidate_set_card φ (mixedCandidateResources R) σ c (hinj c.val.1 c.val.2)]
    exact hsize c.val.1 c.val.2
  · intro c;exact hw c.val.1 c.val.2
  · intro x
    have hh:=physical_mixed_sampled_degree_from_targets φ R w σ hinj M hM target τ t ht htarget hload x
    have hb:=abs_le.mp (hh.trans herr)
    exact ⟨by linarith,by linarith⟩
  · intro x y hxy
    have hne:x.val≠y.val:=fun h=>hxy (Subtype.ext h)
    have hh:=physical_sampled_candidate_codegree_le φ (mixedCandidateResources R) (mixedCandidateWeight w) σ
      (fun c=>hw c.1 c.2) x y
    apply hh.trans
    have hh':(∑c:Σ i,E i,if x.val∈Rphys c.1 c.2 ∧ y.val∈Rphys c.1 c.2 then w c.1 c.2 else 0)≤
        (∑i,(M:ℝ)^2*Ki i)/n:=hfull x.val y.val hne
    exact hh'.trans (div_le_div_of_nonneg_right hKsum hn0.le)
  · exact hS
  · exact hg
  · exact hmass
end Oberwolfach
