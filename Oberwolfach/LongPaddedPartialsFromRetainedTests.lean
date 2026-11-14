module

public import Oberwolfach.LongPaddedPartialsFromMatchingTests
public import Oberwolfach.LongRetainedHubTestsFromPatterns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] longPaddedFromTestsFinDecidable
attribute [local instance] longPaddedFromTestsSelectedFintype
attribute [local instance] longPaddedFromTestsAtHubFintype
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

theorem long_padded_safe_partials_from_retained_hub_matching_tests
    (hn:0<n) (hu:Fintype.card U≤n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (hK3:3≤K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hlong:∀u,(1/2:ℝ)≤((Finset.univ.filter (fun v=>K<Fintype.card ((F u).connectedComponentMk v))).card:ℝ)/n)
    (τ A BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (ret:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) ret)
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
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false ret J false false
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
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
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val*mixedCandidateWeight W c.val
      (1-γ)*mass≤∑c∈M,test c.val)→
    (∀z:LongRetainedHubTest F hF K θ,
      let test:=longRetainedHubIndicator F hF θ hub z
      let mass:=∑c:RestrictedResource (mixedCandidateResources R) e,
        test c.val*mixedCandidateWeight W c.val
      (∑c∈M,test c.val)≤(1+γ)*mass)→
    let T:=bernoulliVertexSet state
    let eraw:{z // z∈T}↪_:=Function.Embedding.subtype _
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let N:=M.map q
    let A:=LongRawSelectedOrdinary π d m ℓ eraw N
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ eraw N
    ∃assign:A↪(Σu,(F u).ConnectedComponent),
    ∃C:∀a:A,(F (Q a).val.2).ConnectedComponent,
      (∀a,(⟨(Q a).val.2,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
    (∀u,Fintype.card (longRawSourceDomain F π d m ℓ eraw N C u) =
      ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u} =
      n - ∑i:Fin K,(N.filter (fun c=>c.val.1=some i ∧
        longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card * ℓ i) ∧
    (∀u,|((Fintype.card (longRawSourceDomain F π d m ℓ eraw N C u):ℕ):ℝ) -
      (1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u)| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u,|((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u}:ℕ):ℝ) -
      ((n:ℝ)-(1-θ)*(n:ℝ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u))| ≤
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u, (n:ℝ)*ordinaryAssignedFraction F hF K u none -
      ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ)) ≤
        ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u}:ℕ):ℝ) ∧
      ((Fintype.card {v:Fin n // v∉longRawSourceDomain F π d m ℓ eraw N C u}:ℕ):ℝ) ≤
        (n:ℝ)*(ordinaryAssignedFraction F hF K u none+(101/100:ℝ)*θ) +
          ((max (3*eps) 0)*(n:ℝ))*(∑i:Fin K,((ℓ i:ℕ):ℝ))) ∧
    (∀u v,K<Fintype.card ((F u).connectedComponentMk v)→
      v∉longRawSourceDomain F π d m ℓ eraw N C u) ∧
    let T:=longRawSourceDomain F π d m ℓ eraw N C
    ∃ψ:∀u,(T u)↪Fin n,
      (∀u x y,(F u).Adj x.val y.val→
        rawMarkedPairRims P π d raw (Sum.inl (ψ u x,ψ u y)) ∨
        rawMarkedPairRims P π d raw (Sum.inl (ψ u y,ψ u x))) ∧
      (∀u v,u≠v→Disjoint
        (partialFactorPhysicalEdges (T u) ((F u).induce (T u)) (ψ u))
        (partialFactorPhysicalEdges (T v) ((F v).induce (T v)) (ψ v))) ∧
      (∀u x y,(F u).Adj x.val y.val→Sum.inl ({ψ u x,ψ u y}:Finset (Fin n))∉Reserve) ∧
      (∀u x y,(F u).Adj x.val y.val→s(ψ u x,ψ u y)∉Del.edgeFinset) :=by
  intro ni hni selected H raw pstar BMseed BOseed C ℓ Wm Wo W R state hload hcount Del δ hDel herr0 herrle rawDeleted newState hub S e habs M hpos hmatch hlow hup
  have h:=long_padded_safe_partials_from_surviving_matching_tests hn hu F hF Allowed hAllowed K hK hK3 m d hm hd θ ρ₀ ρ D hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π hlong τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper σ ret J Reserve X Z p k τerr t countErr γ eps lam hθpos hlam hlamθ hepsAssign hθ1 hb hτerr hcount0 hcountle hγ hγε heps heps1
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
