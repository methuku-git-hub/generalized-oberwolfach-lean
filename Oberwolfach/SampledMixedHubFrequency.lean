module

public import Oberwolfach.MixedMatchedHubFrequency
public import Oberwolfach.SampledResourceSubsetCard
public import Oberwolfach.RestrictedSampledRootLoads

@[expose] public section
/-! The original root-omitted potential estimates and fixed-domain counts
supply the matching frequency estimate on the sampled ground set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U:Type} [Fintype I] [Fintype V] [Fintype U] [DecidableEq I] [DecidableEq V] [DecidableEq U]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem sampled_mixed_hub_frequency_from_patterns
    (R:∀j,E j→Finset V) (state:V→Bool) (w:∀j,E j→ℝ) (hub:∀j,E j→U)
    (i:I) (u:U) (S:Finset V) (r:ℕ) (hr:0<r)
    (hS:∀c,(R i c∩S).card=if hub i c=u then r else 0)
    (η s n err countErr γ θ f:ℝ) (hη:0≤η) (hγ:0≤γ) (hbalance:η*s=(1-θ)*f)
    (hdeg:∀v∈S,state v=true→|resourcePatternLoad (R i) (w i) (fun _ _=>true) v state-η|≤err)
    (hcount:|((S.filter (fun v=>state v=true)).card:ℝ)-s*n|≤countErr)
    (hweight:∀j c,0≤w j c):
    let e:{v:V // v∈bernoulliVertexSet state}↪V:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    let test:=mixedHubIndicator hub i u
    let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
      test c.val.1 c.val.2*mixedCandidateWeight w c.val
    (1-γ)*mass≤∑c∈M,test c.val.1 c.val.2→
    (∑c∈M,test c.val.1 c.val.2)≤(1+γ)*mass→
    |((M.filter (fun c=>c.val.1=i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-(1-θ)*f*n/r|≤
      (((S.filter (fun v=>state v=true)).card:ℝ)*err+η*countErr+
       γ*(|(1-θ)*f*n|+(((S.filter (fun v=>state v=true)).card:ℝ)*err+η*countErr)))/r :=by
  intro e M test mass hlow hup
  have hdeg':∀v∈restrictedResourceSubset e S,
      |hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v-η|≤err:=by
    intro v hv
    rw [sampled_resource_degree_eq_pattern]
    exact hdeg v.val (Finset.mem_filter.mp hv).2 ((mem_bernoulliVertexSet state v.val).mp v.property)
  have hcard:(restrictedResourceSubset e S).card=(S.filter (fun v=>state v=true)).card:=
    sampled_resource_subset_card_filter state S
  have hcount':|((restrictedResourceSubset e S).card:ℝ)-s*n|≤countErr:=by rw [hcard];exact hcount
  have h:=mixed_matched_family_hub_frequency R e w i hub u S r hr hS η s n err countErr γ θ f hη hγ hbalance hdeg' hcount' hweight M hlow hup
  simpa only [hcard] using h
end Oberwolfach
