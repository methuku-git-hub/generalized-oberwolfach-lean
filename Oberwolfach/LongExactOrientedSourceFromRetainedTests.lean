module

public import Oberwolfach.LongExactOrientedSourceFromMatchingTests
public import Oberwolfach.LongOrientedSourceFromMatchingTests
public import Oberwolfach.LongProtectedSourceFromMatchingTests
public import Oberwolfach.LongAlignedSourceFromMatchingTests
public import Oberwolfach.LongPaddedMapsFromRetainedTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longExactOrientedSourceFromRetainedTestsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_exact_oriented_source_from_retained_matching_tests
    (hn:0<n) (hU:0<Fintype.card U) (hu:Fintype.card U≤n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (hK3:3≤K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hcutSource:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:8*((m:ℝ)+1)/θ<(n:ℝ)^((1:ℝ)/4))
    (τ A BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (hraw:raw=(fun e=>rawExpandedApproximateCollapse e (σ e))) (ret:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) ret)
    (hstarts:∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(n:ℝ)^(3/4:ℝ)/d)
    (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U)
    (p k τerr t countErr γ eps lam:ℝ)
    (hθpos:0<θ) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hθ1:θ≤1) (hb:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hτerr:0≤τerr) (hcount0:0≤countErr) (hcountle:4*countErr≤(eps/2)*n)
    (hγ:0≤γ) (hγε:γ≤eps) (heps:0≤eps) (heps1:eps≤1):
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false ret J false false
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let C:=10*(((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d m ℓ
    let state:=longRawHubState P π d raw true true
    (∀(i:Option (Fin K)) (root:LongRawHubResource n U),state root=true→
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K m θ D p k i root|≤
        t+τerr*longAssignedMixedTarget F hF K m θ D p k i root)→
    (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun v=>state v=true)).card:ℝ)-
      longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤countErr)→
    ∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
    (0≤t+C*(δ/(n:ℝ))+4*τerr)→(t+C*(δ/(n:ℝ))+4*τerr≤eps/2)→
    let rawDeleted:=rawMarkedDeleteRims raw Del.edgeFinset
    let newState:=longRawHubState P π d rawDeleted true true
    let hub:=longRawHubNames (U:=U) π d m ℓ
    let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let e:{v // v∈S}↪_:=Function.Embedding.subtype _
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z →
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,0<mixedCandidateWeight W c.val) →
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c')) →
    (∀z:LongRetainedHubTest F hF K θ,
      let test:=longRetainedHubIndicator F hF θ hub z
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,test c.val*mixedCandidateWeight W c.val
      (1-γ)*mass≤∑c∈M,test c.val)→
    (∀z:LongRetainedHubTest F hF K θ,
      let test:=longRetainedHubIndicator F hF θ hub z
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,test c.val*mixedCandidateWeight W c.val
      (∑c∈M,test c.val)≤(1+γ)*mass)→
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    LongSelectedExactOrientedSourceOutcome hU F P π d m ℓ raw ret J σ N :=by
  subst raw
  intro ni hni selected H pstar BMseed BOseed C ℓ Wm Wo W R state hload hcount Del δ hDel herr0 herrle rawDeleted newState hub S e habs M hpos hmatch hlow hup T eraw q N
  let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
  have h:=long_exact_oriented_source_from_surviving_matching_tests hn hU hu F hF Allowed hAllowed K hK hK3 m d hm hd θ ρ₀ ρ D hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π hnoshort hcutSource hlarge τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper σ raw rfl ret J hstarts Reserve X Z p k τerr t countErr γ eps lam hθpos hlam hlamθ hepsAssign hθ1 hb hτerr hcount0 hcountle hγ hγε heps heps1
  apply h hload hcount Del δ hDel herr0 herrle habs M hpos hmatch
  · intro i u hi
    have hh:=hlow ⟨(i,u),hi⟩
    dsimp only [longRetainedHubIndicator] at hh
    have hdec : instDecidableEqFin K = longPaddedFromTestsFinDecidable K := Subsingleton.elim _ _
    rw [hdec] at hh
    exact hh
  · intro i u hi
    have hh:=hup ⟨(i,u),hi⟩
    dsimp only [longRetainedHubIndicator] at hh
    have hdec : instDecidableEqFin K = longPaddedFromTestsFinDecidable K := Subsingleton.elim _ _
    rw [hdec] at hh
    exact hh
end Oberwolfach
