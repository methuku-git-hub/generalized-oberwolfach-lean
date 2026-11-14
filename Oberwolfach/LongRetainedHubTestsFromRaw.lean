module

public import Oberwolfach.LongRetainedHubTestsFromTargets
public import Oberwolfach.LongMixedActualHubCounts
public import Oberwolfach.RawOrdinaryHubCountInCommonState

@[expose] public section
/-! The actual mixed candidate families have large retained hub tests on
the raw approximate outcome, using its original root and hub counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_retained_hub_tests_mass_from_raw
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (hK:0<K) (hK3:3≤K) (θ D p k:ℝ) (hθ0:0<θ) (hθ:θ≤1/2)
    (b:U→ℝ) (hbdef:∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (g j:Bool)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (longAssignedPaddedLength i)→ℝ)
    (τ t countErr:ℝ) (hτ:τ≤1/2) (ht:t≤θ/(800*(K:ℝ))):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let R:=longMixedSeedResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun _ (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longAssignedPaddedLength _))=>orderedOrdinaryResources W)
    let w:=longMixedSeedWeight wM wO
    let hub:=longMixedWheelHub (U:=U) π (3*d) m
    (∀j v,v∈bernoulliVertexSet state→
      |resourcePatternLoad (R j) (w j) (fun _ _=>true) v state-
        longAssignedMixedTarget F hF K m θ D p k j v|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p k j v)→
    (letI:DecidableEq (Fin n):=Classical.decEq _; ∀u,|rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) g j false u Finset.univ-b u*n|≤countErr)→
    countErr≤pstar*n/2→
    let e: {v // v∈bernoulliVertexSet state}↪_ := Function.Embedding.subtype _
    ∀z:LongRetainedHubTest F hF K θ,
      θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤
        ∑c:RestrictedResource (mixedCandidateResources R) e,
          longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight w c.val :=by
  intro raw state R w hub hload hcount hcountErr e
  have hS:∀i u c,(R (some i) c∩ordinaryCommonHubSpokeRoots u).card=
      if hub (some i) c=u then longAssignedPaddedLength i else 0:=by
    intro i u c
    exact long_mixed_ordinary_hub_spoke_count π (3*d) m i u c
  have hcount':∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-b u*n|≤countErr:=by
    intro u
    rw [expanded_raw_ordinary_common_hub_sample_count P π d σ g j u]
    exact hcount u
  exact long_retained_hub_tests_mass_from_mixed_targets hn F hF m hK hK3 θ D p k hθ0 hθ
    b hbdef hb pstar hpstar hbstar R state w hub hS τ t countErr hτ ht hload hcount' hcountErr
end Oberwolfach
