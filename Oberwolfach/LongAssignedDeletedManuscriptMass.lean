module

public import Oberwolfach.LongRetainedHubTestsManuscriptTargets
public import Oberwolfach.LongAssignedRawDeletedEventLoads
public import Oberwolfach.LongAssignedSeedFunctionBounds
public import Oberwolfach.LongAssignedMixedPhysicalDeletion
public import Oberwolfach.LongMixedDeletionUniformConstant
public import Oberwolfach.LongAssignedCommonEventDeletionLoads
public import Oberwolfach.LongRawDeletedStateBool
public import Oberwolfach.LongRawDeletedHubSpokeCounts
public import Oberwolfach.LongRetainedHubTestsFromTargets

@[expose] public section
/-! Uniform positive constants for the named actual seed functions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_manuscript_test_mass_after_every_deletion
    (hn:0<n) (hu:Fintype.card U≤n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (τ A BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (hK3:3≤K) (hθpos:0<θ)
    (hpadded:∀i,ni i+2=longAssignedPaddedLength i)
    (p k τerr t countErr pmin:ℝ) (hτerr:τerr≤1/16)
    (b:U→ℝ) (hbdef:∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hb:∀u,0<b u ∧ b u≤1) (hpmin:0<pmin) (hbmin:∀u,pmin≤b u)
    (hcountErr:countErr≤pmin*n/16):
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let C:=10*(((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d m ℓ
    let state:=longRawHubState P π d raw g j
    (∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K m θ D p k i root|≤
        t+τerr*longAssignedMixedTarget F hF K m θ D p k i root)→
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-b u*n|≤countErr)→
    ∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
    (t+C*(δ/(n:ℝ))≤θ/(3200*(K:ℝ)))→
    let rawDeleted:=rawMarkedDeleteRims raw Del.edgeFinset
    let newState:=longRawHubState P π d rawDeleted g j
    let hub:=longRawHubNames (U:=U) π d m ℓ
    let e:{v // v∈bernoulliVertexSet newState}↪_:=Function.Embedding.subtype _
    ∀z:LongRetainedHubTest F hF K θ,
      θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
        ∑c:RestrictedResource (mixedCandidateResources R) e,
          longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight W c.val :=by
  intro pstar BMseed BOseed C ℓ Wm Wo W R state hload hcount Del δ hDel ht rawDeleted newState hub e
  have hpost:=long_assigned_common_event_raw_deleted_loads hn hu F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper raw g j
    (longAssignedMixedTarget F hF K m θ D p k) (fun i root=>t+τerr*longAssignedMixedTarget F hF K m θ D p k i root)
    hload Del δ hDel
  have hc:∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>newState v=true)).card:ℝ)-b u*n|≤countErr:=by
    intro u
    rw [long_raw_ordinary_hub_spoke_count_after_rim_deletion P π d raw g j Del.edgeFinset u]
    exact hcount u
  have hS:∀i u c,(R (some i) c∩ordinaryCommonHubSpokeRoots u).card=
      if hub (some i) c=u then longAssignedPaddedLength i else 0:=by
    intro i u c
    have hh:=long_raw_hub_context_spokes π d m ℓ i u c
    have hp:ℓ i=longAssignedPaddedLength i:=hpadded i
    rw [hp] at hh
    convert hh using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have htarget:∀i v,v∈bernoulliVertexSet newState→
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) v newState-
        longAssignedMixedTarget F hF K m θ D p k i v|≤
        (t+C*(δ/(n:ℝ)))+τerr*longAssignedMixedTarget F hF K m θ D p k i v:=by
    intro i v hv
    have hh:=hpost i v ((mem_bernoulliVertexSet newState v).mp hv)
    linarith
  have hθtenth:θ≤1/10:=by linarith
  exact long_retained_hub_tests_manuscript_mass_from_mixed_targets hn F hF m hK hK3 θ D p k hθpos hθtenth
    b hbdef hb pmin hpmin hbmin R newState W hub hS τerr (t+C*(δ/(n:ℝ))) countErr hτerr ht htarget hc hcountErr
end Oberwolfach
