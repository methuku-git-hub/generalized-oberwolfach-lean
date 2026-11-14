module

public import Oberwolfach.LongAssignedDeletedRetainedMass
public import Oberwolfach.RestrictedResourceEqualStateEquiv
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

theorem long_assigned_surviving_retained_test_mass_after_every_deletion
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
    (p k τerr t countErr pmin:ℝ) (hτerr:τerr≤1/2)
    (b:U→ℝ) (hbdef:∀u,b u=longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hb:∀u,0<b u ∧ b u≤1) (hpmin:0<pmin) (hbmin:∀u,pmin≤b u)
    (hcountErr:countErr≤pmin*n/2):
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
    (t+C*(δ/(n:ℝ))≤θ/(800*(K:ℝ)))→
    let rawDeleted:=rawMarkedDeleteRims raw Del.edgeFinset
    let newState:=longRawHubState P π d rawDeleted g j
    let hub:=longRawHubNames (U:=U) π d m ℓ
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let e:{v // v∈S}↪_:=Function.Embedding.subtype _
    ∀z:LongRetainedHubTest F hF K θ,
      θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤
        ∑c:RestrictedResource (mixedCandidateResources R) e,
          longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight W c.val :=by
  intro pstar BMseed BOseed C ℓ Wm Wo W R state hload hcount Del δ hDel ht rawDeleted newState hub S e z
  let T:=bernoulliVertexSet newState
  have hST:S=T:=long_raw_surviving_state_is_raw_rim_deletion P π d raw g j Del.edgeFinset
  have hh:=long_assigned_retained_test_mass_after_every_deletion hn hu F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper raw g j
    hK3 hθpos hpadded p k τerr t countErr pmin hτerr b hbdef hb hpmin hbmin hcountErr hload hcount Del δ hDel ht z
  have heq:(∑c:RestrictedResource (mixedCandidateResources R) (Function.Embedding.subtype (·∈T)),
      longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight W c.val)=
      ∑c:RestrictedResource (mixedCandidateResources R) e,
        longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight W c.val:=by
    convert equal_state_full_weighted_test_mass (mixedCandidateResources R) S T hST
      (fun c=>longRetainedHubIndicator F hF θ hub z c*mixedCandidateWeight W c) using 1 <;>
      congr 3 <;> exact Subsingleton.elim _ _
  change θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤
        ∑c:RestrictedResource (mixedCandidateResources R) (Function.Embedding.subtype (·∈T)),
          longRetainedHubIndicator F hF θ hub z c.val*mixedCandidateWeight W c.val at hh
  rw [heq] at hh
  exact hh
end Oberwolfach
