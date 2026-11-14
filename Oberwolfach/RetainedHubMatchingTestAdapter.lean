module

public import Oberwolfach.LongAllHubAbsoluteFrequencies
public import Oberwolfach.LongRetainedHubTestsFromPatterns

@[expose] public section
/-! The tests supplied to one weighted matching are exactly the hub
indicators required by the simultaneous frequency estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U V:Type} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
  {E:Option (Fin K)→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem retained_hub_matching_tests_to_indices
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ γ:ℝ)
    (R:∀i,E i→Finset V) (state:V→Bool) (w:∀i,E i→ℝ) (hub:∀i,E i→U):
    let e:{v // v∈bernoulliVertexSet state}↪V:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀z:LongRetainedHubTest F hF K θ,
      (1-γ)*(∑c:RestrictedResource (mixedCandidateResources R) e,
        longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight w c.val)≤
      ∑c∈M,longRetainedHubIndicator F hF θ hub z c.val) →
    (∀z:LongRetainedHubTest F hF K θ,
      (∑c∈M,longRetainedHubIndicator F hF θ hub z c.val)≤
      (1+γ)*(∑c:RestrictedResource (mixedCandidateResources R) e,
        longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight w c.val)) →
    (∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val.1 c.val.2*mixedCandidateWeight w c.val
      (1-γ)*mass≤∑c∈M,test c.val.1 c.val.2) ∧
    (∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val.1 c.val.2*mixedCandidateWeight w c.val
      (∑c∈M,test c.val.1 c.val.2)≤(1+γ)*mass) :=by
  intro e M hlow hup
  constructor <;> intro i u hi
  · exact hlow ⟨(i,u),hi⟩
  · exact hup ⟨(i,u),hi⟩
end Oberwolfach
