module

public import Oberwolfach.PhysicalSampledMixedHubMass
public import Oberwolfach.HubTestMassMargin

@[expose] public section
/-! A retained hub-frequency test has positive physical-candidate mass
from root loads, its sampled spoke count and its exact coefficient balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I A U:Type} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [DecidableEq U]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem physical_sampled_hub_frequency_margin
    (R:∀i,E i→Finset A) (σ:A→Bool) (w:∀i,E i→ℝ) (i:I)
    (g:∀j,E j→ℝ) (hub:E i→U) (u:U) (S:Finset A) (r:ℕ)
    (hr:0<r) (hzero:∀j,j≠i→∀c,g j c=0)
    (hg:∀c,g i c=if hub c=u then 1 else 0)
    (hS:∀c,(R i c∩S).card=if hub c=u then r else 0)
    (n s η f fmin θ τ err rmax:ℝ)
    (hn:0≤n) (hs:0<s) (hη:0≤η) (hf:fmin≤f) (hfmin:0≤fmin)
    (hθ:θ≤1/2) (hτ:τ≤1/2) (herr:err≤η/4)
    (hrmax:(r:ℝ)≤rmax) (hbalance:η*s=(1-θ)*f)
    (hdeg:∀v∈S,σ v=true→|resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ-η|≤err+τ*η):
    let e:{v:A // v∈bernoulliVertexSet σ}↪A:=Function.Embedding.subtype _;
    s*n/2≤(restrictedResourceSubset e S).card→
    fmin*n/(16*rmax)≤
      ∑c:PhysicalSampledCandidate (mixedCandidateResources R) σ,
        g c.val.1 c.val.2*mixedCandidateWeight w c.val :=by
  intro e hcount
  let a:ℝ:=(1-τ)*η-err
  have hload:∀v∈S,σ v=true→a≤resourcePatternLoad (R i) (w i) (fun _ _=>true) v σ:=by
    intro v hv hsamp
    have hh:=abs_le.mp (hdeg v hv hsamp)
    dsimp [a]
    nlinarith [hh.1]
  have hm:=physical_sampled_mixed_hub_mass_lower R σ w i g hub u S r hr hzero hg hS a hload
  exact hub_test_mass_margin n s η f fmin θ τ err (restrictedResourceSubset e S).card r rmax _
    hn hs hη hf hfmin hθ hτ herr hcount (by exact_mod_cast hr) hrmax hbalance hm
end Oberwolfach
