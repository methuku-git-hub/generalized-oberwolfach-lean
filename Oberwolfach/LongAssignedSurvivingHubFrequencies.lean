module

public import Oberwolfach.LongAssignedDeletedHubFrequencies
public import Oberwolfach.LongAssignedRawDeletedEventLoads
public import Oberwolfach.RestrictedResourceEqualStateEquiv
public import Oberwolfach.LongAssignedSeedFunctionBounds
public import Oberwolfach.LongAssignedMixedPhysicalDeletion
public import Oberwolfach.LongMixedDeletionUniformConstant
public import Oberwolfach.LongAssignedCommonEventDeletionLoads
public import Oberwolfach.LongRawDeletedStateBool
public import Oberwolfach.LongRawDeletedHubSpokeCounts
public import Oberwolfach.LongRawHubFrequenciesForAssignment

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

theorem long_assigned_surviving_hub_frequencies_after_every_deletion
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
    (p k τerr t countErr γ eps:ℝ)
    (hθ1:θ≤1) (hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hτerr:0≤τerr) (hcount0:0≤countErr) (hcountle:4*countErr≤(eps/2)*n)
    (hγ:0≤γ) (hγε:γ≤eps) (heps:0≤eps) (heps1:eps≤1):
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
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr)→
    ∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
    (0≤t+C*(δ/(n:ℝ))+4*τerr)→(t+C*(δ/(n:ℝ))+4*τerr≤eps/2)→
    let rawDeleted:=rawMarkedDeleteRims raw Del.edgeFinset
    let newState:=longRawHubState P π d rawDeleted g j
    let hub:=longRawHubNames (U:=U) π d m ℓ
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let e:{v // v∈S}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val.1 c.val.2*mixedCandidateWeight W c.val
      (1-γ)*mass≤∑c∈M,test c.val.1 c.val.2)→
    (∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val.1 c.val.2*mixedCandidateWeight W c.val
      (∑c∈M,test c.val.1 c.val.2)≤(1+γ)*mass)→
    ∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      |((M.filter (fun c=>c.val.1=some i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-
        (1-θ)*(longAssignedKeptFraction F hF K θ i u*n/(ℓ i:ℝ))|≤(3*eps)*n :=by
  intro pstar BMseed BOseed C ℓ Wm Wo W R state hload hcount Del δ hDel herr0 herrle rawDeleted newState hub S e M hlow hup
  let T:=bernoulliVertexSet newState
  have hST:S=T:=long_raw_surviving_state_is_raw_rim_deletion P π d raw g j Del.edgeFinset
  let q:=equalStateCandidateEquiv (mixedCandidateResources R) S T hST
  let N:=M.map q.toEmbedding
  have hmass (i:Fin K) (u:U):
      (∑c:RestrictedResource (mixedCandidateResources R) (Function.Embedding.subtype (·∈T)),
        mixedHubIndicator hub (some i) u c.val.1 c.val.2*mixedCandidateWeight W c.val)=
      ∑c:RestrictedResource (mixedCandidateResources R) e,
        mixedHubIndicator hub (some i) u c.val.1 c.val.2*mixedCandidateWeight W c.val:=by
    convert equal_state_full_weighted_test_mass (mixedCandidateResources R) S T hST
      (fun c=>mixedHubIndicator hub (some i) u c.1 c.2*mixedCandidateWeight W c) using 1 <;>
      congr 3 <;> exact Subsingleton.elim _ _
  have hsum (i:Fin K) (u:U):
      (∑c∈N,mixedHubIndicator hub (some i) u c.val.1 c.val.2)=
      ∑c∈M,mixedHubIndicator hub (some i) u c.val.1 c.val.2:=by
    exact equal_state_selected_weighted_test_sum (mixedCandidateResources R) S T hST M
      (fun c=>mixedHubIndicator hub (some i) u c.1 c.2)
  have hl:∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) (Function.Embedding.subtype (·∈T)),
        test c.val.1 c.val.2*mixedCandidateWeight W c.val
      (1-γ)*mass≤∑c∈N,test c.val.1 c.val.2:=by
    intro i u hi
    dsimp only
    rw [hmass i u,hsum i u]
    exact hlow i u hi
  have hu':∀i u,θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u→
      let test:=mixedHubIndicator hub (some i) u
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) (Function.Embedding.subtype (·∈T)),
        test c.val.1 c.val.2*mixedCandidateWeight W c.val
      (∑c∈N,test c.val.1 c.val.2)≤(1+γ)*mass:=by
    intro i u hi
    dsimp only
    rw [hmass i u,hsum i u]
    exact hup i u hi
  have hf:=long_assigned_hub_frequencies_after_every_deletion hn hu F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper raw g j
    p k τerr t countErr γ eps hθ1 hb hτerr hcount0 hcountle hγ hγε heps heps1 hload hcount Del δ hDel herr0 herrle N hl hu'
  intro i u hi
  have hc:((N.filter (fun c=>c.val.1=some i ∧ hub c.val.1 c.val.2=u)).card)=
      ((M.filter (fun c=>c.val.1=some i ∧ hub c.val.1 c.val.2=u)).card):=by
    exact equal_state_candidate_filter_card (mixedCandidateResources R) S T hST M
      (fun c=>c.1=some i ∧ hub c.1 c.2=u)
  have hf':=hf i u hi
  change |((N.filter (fun c=>c.val.1=some i ∧ hub c.val.1 c.val.2=u)).card:ℝ)-
        (1-θ)*(longAssignedKeptFraction F hF K θ i u*n/(ℓ i:ℝ))|≤(3*eps)*n at hf'
  rw [hc] at hf'
  exact hf' 
end Oberwolfach
