module

public import Oberwolfach.MatchingFrequencyAssignmentForm
public import Oberwolfach.LongRawContextHubFrequencies
public import Oberwolfach.LongRawHubContext
public import Oberwolfach.LongAllHubAbsoluteFrequencies

@[expose] public section
/-! The same fixed state and matching simultaneously give all the requested
retained hub-frequency estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]


theorem long_raw_context_hub_frequencies_for_assignment
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k τ t countErr γ eps:ℝ) (hθ0:0≤θ) (hθ1:θ≤1)
    (hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (w:∀i,longRawHubCandidates (U:=U) π d m ℓ i→ℝ) (hr:∀i,0<ℓ i)
    (hτ:0≤τ) (herr0:0≤t+4*τ) (herrle:t+4*τ≤eps/2)
    (hcount0:0≤countErr) (hcountle:4*countErr≤(eps/2)*n)
    (hγ:0≤γ) (hγε:γ≤eps) (heps:0≤eps) (heps1:eps≤1)
    (hload:∀i z,longRawHubState P π d raw g j z=true→
      |resourcePatternLoad (longRawHubResources (U:=U) π d m ℓ (some i)) (w (some i)) (fun _ _=>true) z (longRawHubState P π d raw g j)-
        longAssignedMixedTarget F hF K m θ D p k (some i) z|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p k (some i) z)
    (hcount:∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>longRawHubState P π d raw g j v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr)
    (hw:∀i c,0≤w i c):
    let state:=longRawHubState P π d raw g j
    let R:=longRawHubResources (U:=U) π d m ℓ
    let hub:=longRawHubNames (U:=U) π d m ℓ
    let e:{v // v∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val.1 c.val.2*mixedCandidateWeight w c.val
      (1-γ)*mass≤∑c∈M,test c.val.1 c.val.2) →
    (∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val.1 c.val.2*mixedCandidateWeight w c.val
      (∑c∈M,test c.val.1 c.val.2)≤(1+γ)*mass) →
    ∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      |((M.filter (fun c=>c.val.1=some i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-
        (1-θ)*(longAssignedKeptFraction F hF K θ i u*n/(ℓ i:ℝ))|≤(3*eps)*n :=by
  intro state R hub e M hlow hup i u hi
  have h:=long_raw_context_hub_frequencies hn F hF m θ D p k τ t countErr γ eps hθ0 hθ1 hb
    P π d ℓ raw g j w hr hτ herr0 herrle hcount0 hcountle hγ hγε heps heps1 hload hcount hw M hlow hup i u hi
  exact matching_frequency_assignment_form _ θ _ n (ℓ i) eps h
end Oberwolfach
