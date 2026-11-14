module

public import Oberwolfach.LongRetainedHubTestsManuscriptMass
public import Oberwolfach.LongRetainedHubTestsFromPatterns
public import Oberwolfach.LongOrdinaryHubRootTarget

@[expose] public section
/-! All retained family-and-hub matching test masses follow from the
actual mixed component targets on the common sampled resource state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
  {E:Option (Fin K)→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem long_retained_hub_tests_manuscript_mass_from_mixed_targets
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (hK:0<K) (hK3:3≤K) (θ D p k:ℝ) (hθ0:0<θ) (hθ:θ≤1/10)
    (b:U→ℝ) (hbdef:∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u)
    (R:∀j,E j→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (w:∀j,E j→ℝ) (hub:∀j,E j→U)
    (hS:∀i u c,(R (some i) c∩ordinaryCommonHubSpokeRoots u).card=
      if hub (some i) c=u then longAssignedPaddedLength i else 0)
    (τ t countErr:ℝ) (hτ:τ≤1/16) (ht:t≤θ/(3200*(K:ℝ)))
    (hload:∀j v,v∈bernoulliVertexSet state→
      |resourcePatternLoad (R j) (w j) (fun _ _=>true) v state-
        longAssignedMixedTarget F hF K m θ D p k j v|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p k j v)
    (hcount:∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-b u*n|≤countErr)
    (hcountErr:countErr≤pstar*n/16):
    let e: {v // v∈bernoulliVertexSet state}↪_ := Function.Embedding.subtype _
    ∀z:LongRetainedHubTest F hF K θ,
      θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
        ∑c:RestrictedResource (mixedCandidateResources R) e,
          longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight w c.val :=by
  intro e
  have hdeg:∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      ∀v∈ordinaryCommonHubSpokeRoots u,state v=true→
      |resourcePatternLoad (R (some i)) (w (some i)) (fun _ _=>true) v state-
        longAssignedKeptOrdinaryContribution F hF K θ i u/b u|≤
        t+τ*(longAssignedKeptOrdinaryContribution F hF K θ i u/b u):=by
    intro i u _ v hv hstate
    have h:=hload (some i) v ((mem_bernoulliVertexSet state v).mpr hstate)
    rw [long_assigned_ordinary_hub_root_target F hF K m θ D p k i u v hv] at h
    simpa only [hbdef u] using h
  intro z
  have h:=long_retained_hub_tests_manuscript_mass_from_patterns hn F hF m hK hK3 θ hθ0 hθ b hbdef hb pstar hpstar hbstar
    R state w hub ordinaryCommonHubSpokeRoots hS τ t countErr hτ ht hdeg hcount hcountErr z
  convert h using 1
  apply Finset.sum_congr
  · ext c
    simp only [Finset.mem_univ]
  · intro c _
    rfl
end Oberwolfach
