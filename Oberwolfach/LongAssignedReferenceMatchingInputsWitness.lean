module

public import Oberwolfach.LongAssignedReferenceRetainedMassWitness
public import Oberwolfach.LongAssignedSeedPairBounds
public import Oberwolfach.LongAssignedMixedTargetProfile
public import Oberwolfach.LongAssignedRawDeletedEventLoads
public import Oberwolfach.LongAssignedSurvivingRetainedMass
public import Oberwolfach.LongAssignedActualMixedActiveLoads
public import Oberwolfach.MixedClassMarkedRetentionProjection
public import Oberwolfach.ExpandedApproximateCommonEvents
public import Oberwolfach.LongAssignedSpokeCountTransfer
public import Oberwolfach.LongAssignedNamedSeedCommonEvent
public import Oberwolfach.LongActualRawLawParameters
public import Oberwolfach.LongSeedEvents

@[expose] public section
/-! Joint concentration for the original assigned fixed weights under the
actual expanded law, with an arbitrary prior event on the same retained
experiment. This does not yet discharge the prior-event estimate or identify
all root expectations with the matching target profile. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_reference_matching_inputs_witness
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
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
    (huv:Fintype.card U≤n)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (εHost:ℝ) (hpos:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hp₂:0<(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)
    (hk₂:0<(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D)
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C:OrdinaryCycle P (ni i+2),if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤εHost*n)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+εHost*n≤τ*D)
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ)
    (t:ℝ) (ht:0<t) (tHub:ℝ) (htHub:0<tHub)
    (hK3:3≤K) (hθpos:0<θ) (hτ:τ≤1/2)
    (hpadded:∀i,ni i+2=longAssignedPaddedLength i)
    (hbupper:∀u,longAssignedApproxOrdinaryWeight F hF K m θ u≤1)
    (pmin:ℝ) (hpmin:0<pmin) (hbmin:∀u,pmin≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hcountErr:tHub≤pmin*n/2) (hKle:K≤n)
    (alpha:ℝ) (halpha:0<alpha) (halphaMass:alpha≤θ/(1600*(K:ℝ)*(K:ℝ))) (g₀:Bool):
    let b:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(m:ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(m:ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    let hLaw:=long_assigned_actual_raw_law_parameters hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
      hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>
      rawExpandedMarkedCollapse e (ω e)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let C:=10*(((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d m ℓ
    let Pair:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>((m:ℝ)+1)^4*BMseed
      | some i=>((ni i:ℝ)+2)^3*BOseed i
    let Kpair:=1+((m:ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed i
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*(n:ℝ)))
    letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)) (startRetentionMinimum_le _)
    ∀(Prior:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d g₀→Prop) (ε:ℝ),
    1-ε≤(rawMarkedRetentionLaw π d hd g₀ p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2).probability Prior →
    ε+failure+mixedSeedFailureBound (Fin n) U d m K (fun i=>ni i+1) BMseed BOseed t<1 →
    ∃z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω)),
      0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Prior ⟨f z.1,z.2⟩ ∧
        (∀b u,|rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) true true b u Finset.univ-
          (if b then q u true else s u true)*(n:ℝ)|<tHub) ∧
        (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun root=>
          longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true)).card:ℝ)-
          longAssignedApproxOrdinaryWeight F hF K m θ u*n|≤tHub) ∧
        rawMarkedSeedConcentrated P π d m p₂ k₂ q s true true t Wm
          (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        (∀i,rawOrdinarySeedConcentrated P π d (ni i+2) p₂ k₂ q s true true t (Wo i)
          (fun e=>rawExpandedApproximateCollapse e (z.1 e))) ∧
        (∀i root,longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true→
          |resourcePatternLoad (longRawHubResources (U:=U) π d m (fun i=>ni i+2) i)
            (longMixedSeedWeight Wm Wo i) (fun _ _=>true) root
            (longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true)-
            longAssignedMixedTarget F hF K m θ D p₂ k₂ i root|≤
          t+τ*longAssignedMixedTarget F hF K m θ D p₂ k₂ i root) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          t+C*(δ/(n:ℝ))≤θ/(800*(K:ℝ))→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let hub:=longRawHubNames (U:=U) π d m ℓ
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let e:{v // v∈S}↪_:=Function.Embedding.subtype _
          ∀ztest:LongRetainedHubTest F hF K θ,
            θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤
              ∑c:RestrictedResource (mixedCandidateResources R) e,
                longRetainedHubIndicator F hF θ hub ztest c.val*mixedCandidateWeight W c.val) ∧
        (0<Kpair ∧ (∑i,Pair i)≤Kpair) ∧
        (∀i c,0≤W i c) ∧
        Fintype.card (LongRetainedHubTest F hF K θ)≤n^3 ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          t+C*(δ/(n:ℝ))≤θ/(800*(K:ℝ))→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let state:=longRawHubState P π d (rawMarkedDeleteRims raw Del.edgeFinset) true true
          let hub:=longRawHubNames (U:=U) π d m ℓ
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let e:{v // v∈S}↪_:=Function.Embedding.subtype _
          (∀v,v∈bernoulliVertexSet state→∑i,longAssignedMixedTarget F hF K m θ D p₂ k₂ i v=1) ∧
          (∀i v,v∈bernoulliVertexSet state→
            |resourcePatternLoad (R i) (W i) (fun _ _=>true) v state-
              longAssignedMixedTarget F hF K m θ D p₂ k₂ i v|≤
              (t+C*(δ/(n:ℝ)))+τ*longAssignedMixedTarget F hF K m θ D p₂ k₂ i v) ∧
          (∀i u v,u≠v → resourceOmittedPairWeight (R i) (W i) u v≤Pair i/n) ∧
          (∀(ztest:LongRetainedHubTest F hF K θ) (c:RestrictedResource (mixedCandidateResources R) e),0≤longRetainedHubIndicator F hF θ hub ztest c.val ∧
            longRetainedHubIndicator F hF θ hub ztest c.val≤1) ∧
          (∀ztest:LongRetainedHubTest F hF K θ,
            alpha*(n:ℝ)≤∑c:RestrictedResource (mixedCandidateResources R) e,
              longRetainedHubIndicator F hF θ hub ztest c.val*mixedCandidateWeight W c.val)) :=by
  intro b a p₁ k₁ p₂ k₂ udens q s hLaw μ f pstar BMseed BOseed Wm Wo C ℓ W R Pair Kpair failure Ret ν Prior ε hprior hbudget
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hh:=long_assigned_reference_seed_hub_load_mass_witness hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper
    huv hnoshort εHost hpos hp₂ hk₂ he hdeg hbudgetV hbudgetE t ht tHub htHub hK3 hθpos hτ hpadded hbupper
    pmin hpmin hbmin hcountErr g₀ Prior ε hprior hbudget
  obtain ⟨z,hz,hPrior,hSpoke,hCount,hM,hO,hload,hMass⟩:=hh
  have hBounds:=long_assigned_named_seed_bounds hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper
  have hpair:=long_assigned_named_seed_pair_bounds hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper huv
  have hdecPair : referenceWitnessFinDecidable n = instDecidableEqFin n := Subsingleton.elim _ _
  rw [←hdecPair] at hpair
  have hBMseed:0<BMseed:=hBounds.1
  have hBOseed:∀i,0<BOseed i:=hBounds.2.1
  refine ⟨z,hz,hPrior,hSpoke,hCount,hM,hO,hload,hMass,?_,?_,?_,?_⟩
  · constructor
    · have hsumNonneg:0≤∑i:Fin K,((ni i:ℝ)+2)^3*BOseed i:=by
        apply Finset.sum_nonneg
        intro i _
        have hi:=hBOseed i
        positivity
      have hmarkedNonneg:0≤((m:ℝ)+1)^4*BMseed:=by positivity
      dsimp only [Kpair]
      linarith
    · dsimp [Pair,Kpair]
      simp only [Fintype.sum_option]
      linarith
  · intro i c
    cases i with
    | none => exact (hBounds.2.2.1 c).1
    | some i => exact (hBounds.2.2.2 i c).1
  · have hcard:=long_retained_hub_tests_card_bound F hF K θ huv hKle
    have hn1:1≤n:=by omega
    have hpow:n^2≤n^3:=by nlinarith
    exact hcard.trans hpow
  · intro Del δ hDel hmargin raw state hub S e
    have hdel:=long_assigned_common_event_raw_deleted_loads hn huv F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
      hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper
      raw true true (longAssignedMixedTarget F hF K m θ D p₂ k₂)
      (fun i v=>t+τ*longAssignedMixedTarget F hF K m θ D p₂ k₂ i v)
    have hdec : referenceWitnessFinDecidable n = instDecidableEqFin n := Subsingleton.elim _ _
    rw [←hdec] at hdel
    have hdel:=hdel hload Del δ hDel
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro v _
      exact long_assigned_mixed_target_sum_one F hF K m θ D p₂ k₂ hD hp₂ hpos rfl rfl v
    · intro i v hv
      have h:=hdel i v ((mem_bernoulliVertexSet state v).mp hv)
      linarith
    · intro i u v _
      exact hpair i u v
    · intro ztest c
      exact long_retained_hub_indicator_range F hF θ hub ztest c.val
    · intro ztest
      have ha:alpha*(n:ℝ)≤θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ)):=by
        calc
          alpha*(n:ℝ)≤(θ/(1600*(K:ℝ)*(K:ℝ)))*(n:ℝ):=mul_le_mul_of_nonneg_right halphaMass (Nat.cast_nonneg n)
          _=θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ)):=by ring
      exact ha.trans (hMass Del δ hDel hmargin ztest)
end Oberwolfach
