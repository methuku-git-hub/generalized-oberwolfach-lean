module

public import Oberwolfach.LongAssignedMatchingUniformProbability
public import Oberwolfach.MarkedExpandedDegreeArbitraryFailure
public import Oberwolfach.RawSelectedPhysicalNeighbourTests
public import Oberwolfach.RawSelectedRimTwoPaths
public import Oberwolfach.RawApproximateRimTwoPaths
public import Oberwolfach.LongAssignedReferenceManuscriptUniformExtraEvent
public import Oberwolfach.RawUnassignedPhysicalNeighbourTests
public import Oberwolfach.LongAssignedReferenceManuscriptUniform
public import Oberwolfach.LongAssignedMatchingCoefficients
public import Oberwolfach.LongAssignedJointFailureUniform
public import Oberwolfach.LongAssignmentManuscriptTolerances

@[expose] public section
/-! A single actual retained outcome supports a matching after every later
physical deletion satisfying the displayed original quantitative margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_assigned_matching_colour_expanded_high_probability
    (K m d:ℕ) (hK3:3≤K) (hm:7≤m) (hd:2≤d)
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i) (hpadded:∀i,ni i+2=longAssignedPaddedLength i)
    (θ ρ₀ BM:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hBM:0<BM)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (alpha γ ε₀ eps ηEvent:ℝ) (hηEvent:0<ηEvent) (hε₀:ε₀<1) (heps:0<eps) (halpha:0<alpha) (halphaMass:alpha≤θ/(200*(K:ℝ)*(K:ℝ))) (hγ:0<γ):
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*m+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+((m:ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*(((m:ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧ ∃N:ℕ,∀n:ℕ,∀hn:max N 1≤n,∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (ρ D:ℝ) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (huv:Fintype.card U≤n)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (εHost:ℝ)
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C:OrdinaryCycle P (ni i+2),if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤εHost*n)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+εHost*n≤τ*D)
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ)
    (hτnonneg:0≤τ) (hτbound:τ≤τ₀) (g₀:Bool),
    let t:=t₀
    let tHub:=ξ*(n:ℝ)
    let b:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(m:ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(m:ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    let hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) m d hm hd θ ρ₀ ρ D
      hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
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
    letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) g₀)) (startRetentionMinimum_le _)
    ∀(Prior:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d g₀→Prop),
    1-ε₀≤(rawMarkedRetentionLaw π d hd g₀ p₁ k₁ hLaw.1 hLaw.2.1 (by dsimp only [p₁,k₁]; have hp:=hLaw.2.2.1; have hk:=hLaw.2.2.2.1; have hu:=hLaw.2.2.2.2.1; have hh:=hLaw.2.2.2.2.2.1; linarith)
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2).probability Prior →
    ∀(Extra:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))→Prop),
    1-ηEvent≤(μ.sigma (fun ω=>ν (f ω))).probability Extra →
    1-(ε₀+5*ηEvent) ≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>Prior ⟨f z.1,z.2⟩ ∧ Extra z ∧
        (∀u i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*
          (1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)) ∧
        (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p₁^2-(n:ℝ)^(3/4:ℝ)-
          2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
            0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)) ∧
        (∀j v,|((∑w,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j v w:ℕ):ℝ)-
          markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ udens j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
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
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let hub:=longRawHubNames (U:=U) π d m ℓ
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let e:{v // v∈S}↪_:=Function.Embedding.subtype _
          ∀ztest:LongRetainedHubTest F hF K θ,
            θ*(n:ℝ)/(200*(K:ℝ)*(K:ℝ))≤
              ∑c:RestrictedResource (mixedCandidateResources R) e,
                longRetainedHubIndicator F hF θ hub ztest c.val*mixedCandidateWeight W c.val) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→0≤t+C*(δ/(n:ℝ))+4*τ ∧ t+C*(δ/(n:ℝ))+4*τ≤eps/2) ∧
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          δ≤Δ*n→
          let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
          let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
          let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
          let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
          let Cand:=RestrictedResource (mixedCandidateResources R) e
          let Q:=restrictedResourceSet (mixedCandidateResources R) e
          let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
          let φ:=fS.trans (markedRawSampledPhysicalEmbedding P π d raw true true)
          let hub:=longRawHubNames (U:=U) π d m ℓ
          let test:=fun (j:LongRetainedHubTest F hF K θ) (c:Cand)=>longRetainedHubIndicator F hF θ hub j c.val
          ∃M:Finset Cand,(∀c∈M,0<mixedCandidateWeight W c.val) ∧
            (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
            (∀x,alpha*n≤(rimIncidentResources φ x).card →
              ((rimIncidentResources φ x\M.biUnion Q).card:ℝ)≤γ*(rimIncidentResources φ x).card) ∧
            (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (alpha*n) (γ*(longRawIncidenceSet S i).card)) ∧
            (∀i,alpha*n≤(longRawIncidenceSet S i).card →
              ((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤γ*(longRawIncidenceSet S i).card) ∧
            (∀j,(1-γ)*(∑c,test j c*mixedCandidateWeight W c.val)≤∑c∈M,test j c) ∧
            (∀j,(∑c∈M,test j c)≤(1+γ)*(∑c,test j c*mixedCandidateWeight W c.val)) ∧
            ∀x,((physicalRimResidualGraph (markedRawSampledPhysicalEmbedding P π d raw true true)
              ((M.map (survivingCandidateEmbedding (mixedCandidateResources R) S T
                (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset))).biUnion
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+δ)) :=by
  intro pstar₀ BMseed₀ BOseed₀ Kpair₀ C₀
  obtain ⟨η,hη,t₀,τ₀,Δ₀,ht₀,hτ₀,hτhalf,hΔ₀,N₀,hMain⟩:=
    long_assigned_reference_manuscript_matching_uniform_probability_with_extra_event K m d hK3 hm hd ni hni hpadded θ ρ₀ BM hθpos hθ hρ₀ hBM BO hBO alpha γ halpha halphaMass hγ
  have hps:0<pstar₀:=by dsimp [pstar₀];positivity
  have hBMseed:0<BMseed₀:=by dsimp [BMseed₀];positivity
  have hBOseed:∀i,0<BOseed₀ i:=by intro i;have hi:=hBO i;dsimp [BOseed₀];positivity
  have hC:0≤C₀:=by
    dsimp only [C₀]
    have hs:0≤∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i:=by
      apply Finset.sum_nonneg
      intro i _
      have hi:=hBOseed i
      positivity
    have hm':0≤((m:ℝ)+1)^4*BMseed₀:=by positivity
    linarith
  obtain ⟨t₁,τ₁,Δ₁,ξ,ht₁,htle,hτ₁,hτle,hΔ₁,hΔle,hξ,hξ128,hξeps,herror⟩:=
    long_assignment_manuscript_tolerances_exist t₀ τ₀ Δ₀ C₀ eps ht₀ hτ₀ hΔ₀ hC heps
  have hτhalf':τ₁≤1/16:=hτle.trans hτhalf
  have hgap:0<(1-ε₀)/4:=by linarith
  obtain ⟨N₁,hfailure⟩:=eventually_assigned_seed_spoke_failure_below d m K (fun i=>ni i+1) BMseed₀ BOseed₀ t₁ ξ ηEvent
    hBMseed hBOseed ht₁ hξ hηEvent
  have hgapSmall:0<ηEvent:=hηEvent
  obtain ⟨N₂,hneighbour⟩:=raw_unassigned_selected_neighbour_tests_high_probability d hd (ηEvent) hgapSmall
  obtain ⟨N₃,hpaths⟩:=raw_expanded_selected_rim_two_paths_high_probability d hd (ηEvent) hgapSmall
  obtain ⟨N₄,hcolours⟩:=raw_expanded_marked_colour_degrees_arbitrary_failure (ηEvent) hgapSmall
  refine ⟨η,hη,t₁,τ₁,Δ₁,ξ,ht₁,hτ₁,hτhalf',hΔ₁,hξ,hξeps,max (max (max (max N₀ N₁) N₂) N₃) N₄,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound g₀
  intro t tHub b a p₁ k₁ p₂ k₂ udens q s hLaw μ f pstar BMseed BOseed Wm Wo C ℓ W R Pair Kpair failure Ret ν Prior hprior Extra hExtra
  have hnpos:0<n:=by omega
  have hnposR:0<(n:ℝ):=by exact_mod_cast hnpos
  have hcoeff:=long_assigned_actual_matching_coefficients hnpos F hF Allowed hAllowed K (by omega) m d hm hd θ ρ₀ ρ D hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hpos:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u:=by
    intro u
    have hh:=(hcoeff.1 u).1
    linarith
  have hbupper:∀u,longAssignedApproxOrdinaryWeight F hF K m θ u≤1:=fun u=>(hcoeff.1 u).2
  have hbmin:∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u:=fun u=>(hcoeff.1 u).1
  have htHub:0<tHub:=by dsimp [tHub];positivity
  have hcountErr:tHub≤(1/4:ℝ)*n/16:=by
    dsimp [tHub]
    have hh:=mul_le_mul_of_nonneg_right hξ128 hnposR.le
    nlinarith
  have hN₀:max N₀ 1≤n:=by omega
  have hN₁:N₁≤n:=by omega
  have hsmall:=hfailure n hN₁ U huv
  have hsmall':failure+mixedSeedFailureBound (Fin n) U d m K (fun i=>ni i+1) BMseed BOseed t≤ηEvent:=by
    dsimp only [failure,tHub,t,BMseed,BOseed,pstar,BMseed₀,BOseed₀,pstar₀] at hsmall ⊢
    linarith
  have hN₂:N₂≤Fintype.card (Fin n):=by simp;omega
  have hN₃:N₃≤Fintype.card (Fin n):=by simp;omega
  let NGood:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))=>
    ∀u i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) u
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*
      (1-(∑g,q u g)-(∑j,s u j))|<(n:ℝ)^(3/4:ℝ)
  let PGood:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))=>
    ∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p₁^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)
  let CGood:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))=>
    ∀j v,|((∑w,sampledColourOrientation P (fun e=>z.1 (Sum.inl e)) j v w:ℕ):ℝ)-
      markedExpandedPhysicalProbability p₁ k₁ p₂ k₂ udens j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)
  let Good:=fun z=>((NGood z ∧ PGood z) ∧ CGood z) ∧ Extra z
  have hNeighbour:1-ηEvent≤(μ.sigma (fun ω=>ν (f ω))).probability NGood:=by
    simpa [NGood] using hneighbour (Fin n) hN₂ U Bool Bool (by simpa using huv) P π p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1
      hLaw.2.2.2.2.2.2.2.2.2 hnoshort Ret ν
  have hPaths:1-ηEvent≤(μ.sigma (fun ω=>ν (f ω))).probability PGood:=by
    simpa [PGood] using hpaths (Fin n) hN₃ U Bool Bool P π p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1
      hLaw.2.2.2.2.2.2.2.2.2 Ret ν
  have hN₄:N₄≤Fintype.card (Fin n):=by simp;omega
  have hColour:1-ηEvent≤(μ.sigma (fun ω=>ν (f ω))).probability CGood:=by
    have hh:=hcolours (Fin n) hN₄ U Bool Bool P P p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1 d hd
      q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s hLaw.2.2.2.2.2.2.2.2.1
      hLaw.2.2.2.2.2.2.2.2.2 Ret ν
    apply le_trans hh
    apply finiteLaw_probability_mono
    intro z hz j v
    simpa only [Fintype.card_fin] using (hz j v).1
  have hNP:1-2*(ηEvent)≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>NGood z ∧ PGood z):=by
    have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) NGood PGood (ηEvent) (ηEvent) hNeighbour hPaths
    linarith
  have hNPC:1-3*(ηEvent)≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>(NGood z ∧ PGood z) ∧ CGood z):=by
    have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) (fun z=>NGood z ∧ PGood z) CGood (2*(ηEvent)) (ηEvent) hNP hColour
    linarith
  have hGood:1-4*ηEvent≤(μ.sigma (fun ω=>ν (f ω))).probability Good:=by
    have hh:=finiteLaw_intersection_lower (μ.sigma (fun ω=>ν (f ω))) (fun z=>(NGood z ∧ PGood z) ∧ CGood z) Extra (3*(ηEvent)) (ηEvent) hNPC hExtra
    dsimp [Good]
    linarith
  have hh:=hMain n hN₀ U F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost hpos hcoeff.2.1 hcoeff.2.2 he hdeg hbudgetV hbudgetE t ht₁ htle tHub htHub (hτbound.trans hτle) hbupper (1/4) (by norm_num) hbmin hcountErr g₀ Prior ε₀ hprior Good (4*ηEvent) hGood
  have hbound:1-(ε₀+5*ηEvent)≤1-(ε₀+4*ηEvent)-failure-mixedSeedFailureBound (Fin n) U d m K (fun i=>ni i+1) BMseed BOseed t:=by linarith
  apply hbound.trans
  apply hh.trans
  apply finiteLaw_probability_mono_on_support
  intro z hz hzEvent
  obtain ⟨hPrior,hGoodZ,hSpoke,hCount,hM,hO,hload,hMass,hMatch⟩:=hzEvent
  refine ⟨hPrior,hGoodZ.2,hGoodZ.1.1.1,hGoodZ.1.1.2,hGoodZ.1.2,hSpoke,hCount,hM,hO,hload,?_,?_,?_⟩
  · intro Del δ hDel hsmall
    have hd:δ≤Δ₀*n:=hsmall.trans (mul_le_mul_of_nonneg_right hΔle hnposR.le)
    exact hMass Del δ hDel hd
  · intro Del δ hDel hsmall
    have hδ:0≤δ:=by
      have hh:=hDel ⟨0,hnpos⟩
      exact le_trans (Nat.cast_nonneg _) hh
    have hx:0≤δ/(n:ℝ):=div_nonneg hδ hnposR.le
    have hdiv:δ/(n:ℝ)≤Δ₁:=(div_le_iff₀ hnposR).2 (by simpa [mul_comm] using hsmall)
    have herr:=herror t τ (δ/(n:ℝ)) ht₁.le le_rfl hτnonneg hτbound hx hdiv
    simpa only [C,C₀,pstar,pstar₀,BMseed,BMseed₀,BOseed,BOseed₀] using herr
  · intro Del δ hDel hsmall
    have hd:δ≤Δ₀*n:=hsmall.trans (mul_le_mul_of_nonneg_right hΔle hnposR.le)
    exact hMatch Del δ hDel hd
end Oberwolfach
