module

public import Oberwolfach.LongAssignedRawDeletedEventLoads
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

theorem long_assigned_hub_frequencies_after_every_deletion
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
    let e:{v // v∈bernoulliVertexSet newState}↪_:=Function.Embedding.subtype _
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
  intro pstar BMseed BOseed C ℓ Wm Wo W R state hload hcount Del δ hDel herr0 herrle rawDeleted newState hub e M hlow hup
  have hpost:=long_assigned_common_event_raw_deleted_loads hn hu F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper raw g j
    (longAssignedMixedTarget F hF K m θ D p k) (fun i root=>t+τerr*longAssignedMixedTarget F hF K m θ D p k i root)
    hload Del δ hDel
  have hc:∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>newState v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr:=by
    intro u
    rw [long_raw_ordinary_hub_spoke_count_after_rim_deletion P π d raw g j Del.edgeFinset u]
    exact hcount u
  have hwpos:∀i c,0≤W i c:=by
    have hh:=long_assigned_named_seed_bounds hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
      hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper
    intro i c
    cases i with
    | none => exact (hh.2.2.1 c).1
    | some i => exact (hh.2.2.2 i c).1
  apply long_raw_context_hub_frequencies_for_assignment hn F hF m θ D p k τerr (t+C*(δ/(n:ℝ))) countErr γ eps hθ0 hθ1 hb
    P π d ℓ rawDeleted g j W (by intro i;dsimp [ℓ];omega) hτerr herr0 herrle hcount0 hcountle hγ hγε heps heps1 ?_ hc hwpos M hlow hup
  intro i z hz
  have hh:=hpost (some i) z hz
  linarith
end Oberwolfach
