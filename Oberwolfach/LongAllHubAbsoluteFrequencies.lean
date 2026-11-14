module

public import Oberwolfach.LongOrdinaryHubAbsoluteFrequency

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
  {E:Option (Fin K)→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem long_all_hub_absolute_frequencies
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k τ t countErr γ eps:ℝ) (hθ0:0≤θ) (hθ1:θ≤1)
    (hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (R:∀i,E i→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (w:∀i,E i→ℝ) (hub:∀i,E i→U) (r:Fin K→ℕ) (hr:∀i,0<r i)
    (hS:∀i u c,(R (some i) c∩ordinaryCommonHubSpokeRoots u).card=if hub (some i) c=u then r i else 0)
    (hτ:0≤τ) (herr0:0≤t+4*τ) (herrle:t+4*τ≤eps/2)
    (hcount0:0≤countErr) (hcountle:4*countErr≤(eps/2)*n)
    (hγ:0≤γ) (hγε:γ≤eps) (heps:0≤eps) (heps1:eps≤1)
    (hload:∀i z,state z=true→
      |resourcePatternLoad (R (some i)) (w (some i)) (fun _ _=>true) z state-
        longAssignedMixedTarget F hF K m θ D p k (some i) z|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p k (some i) z)
    (hcount:∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr)
    (hw:∀i c,0≤w i c):
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
        (1-θ)*longAssignedKeptFraction F hF K θ i u*n/(r i:ℝ)|≤3*eps*n :=by
  intro e M hlow hup i u hi
  apply long_ordinary_hub_absolute_frequency hn F hF m θ D p k τ t countErr γ eps hθ0 hθ1 hb
    R state w hub i u (r i) (hr i) (hS i u) hτ herr0 herrle hcount0 hcountle hγ hγε heps heps1
    (hload i) (hcount u) hw M
  · convert hlow i u hi using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  · convert hup i u hi using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
