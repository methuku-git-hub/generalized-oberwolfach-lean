module

public import Oberwolfach.MixedMatchedHubCount
public import Oberwolfach.MatchingFrequencyError

@[expose] public section
/-! Matching produces the prescribed family-and-hub count, with its explicit
root-load, hub-count, and matching errors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V W U:Type} [Fintype I] [Fintype V] [Fintype W] [DecidableEq I]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] {E:I→Type}
  [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_matched_family_hub_frequency
    (R:∀i,E i→Finset V) (e:W↪V) (w:∀i,E i→ℝ) (i:I)
    (hub:∀j,E j→U) (u:U) (S:Finset V) (r:ℕ) (hr:0<r)
    (hS:∀c,(R i c∩S).card=if hub i c=u then r else 0)
    (η s n err countErr γ θ f:ℝ) (hη:0≤η) (hγ:0≤γ)
    (hbalance:η*s=(1-θ)*f)
    (hdeg:∀v∈restrictedResourceSubset e S,
      |hypergraphWeightedDegree (restrictedResourceSet (R i) e) (fun c=>w i c.val) v-η|≤err)
    (hcount:|((restrictedResourceSubset e S).card:ℝ)-s*n|≤countErr)
    (hweight:∀j c,0≤w j c)
    (M:Finset (RestrictedResource (mixedCandidateResources R) e)):
    let g:=mixedHubIndicator hub i u
    let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
      g c.val.1 c.val.2*mixedCandidateWeight w c.val
    let actual:=∑c∈M,g c.val.1 c.val.2
    let error:=(restrictedResourceSubset e S).card*err+η*countErr
    (1-γ)*mass≤actual→actual≤(1+γ)*mass→
    |((M.filter (fun c=>c.val.1=i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-(1-θ)*f*n/r|
      ≤(error+γ*(|(1-θ)*f*n|+error))/r:=by
  intro g mass actual error hlow hup
  have h:=mixed_matched_family_hub_count R e w i hub u S r hS η s n err countErr γ hη hγ hdeg hcount hweight M hlow hup
  exact matching_frequency_error r _ η s n θ f error γ (by exact_mod_cast hr) hbalance h
end Oberwolfach
