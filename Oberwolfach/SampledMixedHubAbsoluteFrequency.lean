module

public import Oberwolfach.SampledMixedHubFrequency
public import Oberwolfach.MatchingQuotientFrequencyMargin

@[expose] public section
/-! Uniform absolute matching-frequency errors from the original sampled
root loads and fixed-hub spoke counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U:Type} [Fintype I] [Fintype V] [Fintype U] [DecidableEq I] [DecidableEq V] [DecidableEq U]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem sampled_mixed_hub_absolute_frequency
    (R:∀j,E j→Finset V) (state:V→Bool) (w:∀j,E j→ℝ) (hub:∀j,E j→U)
    (i:I) (u:U) (S:Finset V) (r:ℕ) (hr:0<r)
    (hS:∀c,(R i c∩S).card=if hub i c=u then r else 0)
    (η ηmax s n err countErr γ θ f eps:ℝ) (hη:0≤η) (hη1:η≤ηmax) (hn:0≤n)
    (hγ:0≤γ) (hγε:γ≤eps) (heps:0≤eps) (heps1:eps≤1) (hbalance:η*s=(1-θ)*f)
    (hdeg:∀v∈S,state v=true→|resourcePatternLoad (R i) (w i) (fun _ _=>true) v state-η|≤err)
    (hcount:|((S.filter (fun v=>state v=true)).card:ℝ)-s*n|≤countErr)
    (hq:((S.filter (fun v=>state v=true)).card:ℝ)≤n)
    (herr:0≤err) (herrle:err≤eps/2) (hcount0:0≤countErr) (hcountle:ηmax*countErr≤(eps/2)*n)
    (htarget:|(1-θ)*f*n|≤n) (hweight:∀j c,0≤w j c):
    let e:{v:V // v∈bernoulliVertexSet state}↪V:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    let test:=mixedHubIndicator hub i u
    let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
      test c.val.1 c.val.2*mixedCandidateWeight w c.val
    (1-γ)*mass≤∑c∈M,test c.val.1 c.val.2→
    (∑c∈M,test c.val.1 c.val.2)≤(1+γ)*mass→
    |((M.filter (fun c=>c.val.1=i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-(1-θ)*f*n/r|≤3*eps*n :=by
  intro e M test mass hlow hup
  have habs:=sampled_mixed_hub_frequency_from_patterns R state w hub i u S r hr hS η s n err countErr γ θ f
    hη hγ hbalance hdeg hcount hweight M hlow hup
  let q:ℝ:=((S.filter (fun v=>state v=true)).card:ℝ)
  let error:=q*err+η*countErr
  have he:=hub_frequency_error_budget q n η ηmax err countErr eps (by positivity) hq hη hη1 herr herrle hcount0 hcountle
  exact matching_frequency_quotient_margin r _ n θ f error γ eps (by exact_mod_cast hr) hn heps heps1 hγ hγε he.1 he.2 htarget habs
end Oberwolfach
