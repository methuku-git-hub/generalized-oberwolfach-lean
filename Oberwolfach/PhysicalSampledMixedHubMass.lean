module

public import Oberwolfach.PhysicalSampledRestrictedEquiv
public import Oberwolfach.MixedRestrictedHubMass
public import Oberwolfach.RestrictedSampledRootLoads

@[expose] public section
/-! Hub-test mass for the physical matching candidates is controlled by
the typed root loads on the same realized sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I A U:Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [DecidableEq U]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem physical_sampled_mixed_hub_mass_lower
    (R:∀i,E i→Finset A) (σ:A→Bool) (w:∀i,E i→ℝ) (i:I)
    (g:∀j,E j→ℝ) (hub:E i→U) (u:U) (S:Finset A) (r:ℕ)
    (hr:0<r) (hzero:∀j,j≠i→∀c,g j c=0)
    (hg:∀c,g i c=if hub c=u then 1 else 0)
    (hS:∀c,(R i c∩S).card=if hub c=u then r else 0)
    (a:ℝ) (hdeg:∀v∈S,σ v=true→a≤resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ):
    let e:{v:A // v∈bernoulliVertexSet σ}↪A:=Function.Embedding.subtype _;
    a*((restrictedResourceSubset e S).card:ℝ)/(r:ℝ)≤
      ∑c:PhysicalSampledCandidate (mixedCandidateResources R) σ,
        g c.val.1 c.val.2*mixedCandidateWeight w c.val :=by
  intro e
  have hdeg':∀v∈restrictedResourceSubset e S,
      a≤hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v:=by
    intro v hv
    rw [sampled_resource_degree_eq_pattern]
    apply hdeg v.val
    · exact (Finset.mem_filter.mp hv).2
    · exact (mem_bernoulliVertexSet σ v.val).mp v.property
  have hh:=mixed_restricted_hub_test_mass_lower R e w i g hub u S r hr hzero hg hS a hdeg'
  have heq:=physical_sampled_restricted_sum (mixedCandidateResources R) σ
    (fun c=>g c.1 c.2*mixedCandidateWeight w c)
  exact hh.trans_eq heq.symm
end Oberwolfach
