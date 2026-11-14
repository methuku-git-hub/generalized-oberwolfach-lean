module

public import Oberwolfach.LongAssignedReferenceMatchingInputsWitness
public import Oberwolfach.LongRawMatchingAllIncidences

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

theorem long_assigned_reference_matching_after_deletion
    (K m d:ℕ) (hK3:3≤K) (hm:7≤m) (hd:2≤d)
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i) (hpadded:∀i,ni i+2=longAssignedPaddedLength i)
    (θ ρ₀ BM:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hBM:0<BM)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (alpha γ:ℝ) (halpha:0<alpha) (halphaMass:alpha≤θ/(1600*(K:ℝ)*(K:ℝ))) (hγ:0<γ):
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*m+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+((m:ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    ∃η:ℝ,0<η ∧ ∃N:ℕ,∀n:ℕ,∀hn:max N 1≤n,∀(U:Type) [Fintype U] [DecidableEq U],
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
    (t:ℝ) (ht:0<t) (tHub:ℝ) (htHub:0<tHub) (hτ:τ≤1/2)
    (hbupper:∀u,longAssignedApproxOrdinaryWeight F hF K m θ u≤1)
    (pmin:ℝ) (hpmin:0<pmin) (hbmin:∀u,pmin≤longAssignedApproxOrdinaryWeight F hF K m θ u)
    (hcountErr:tHub≤pmin*n/2) (g₀:Bool),
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
        (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
          t+C*(δ/(n:ℝ))≤θ/(800*(K:ℝ))→
          ((K:ℝ)+1)*(t+C*(δ/(n:ℝ)))+τ≤η→
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
                (restrictedResourceSet (mixedCandidateResources R) (Function.Embedding.subtype (·∈T))))).degree x:ℝ)≤max alpha γ*n+δ) :=by
  intro pstar₀ BMseed₀ BOseed₀ Kpair₀
  have hps:0<pstar₀:=by dsimp [pstar₀]; positivity
  have hBMseed:0<BMseed₀:=by dsimp [BMseed₀]; positivity
  have hBOseed:∀i,0<BOseed₀ i:=by intro i;have hi:=hBO i;dsimp [BOseed₀];positivity
  have hpairpos:0<Kpair₀:=by
    have hs:0≤∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i:=by
      apply Finset.sum_nonneg
      intro i _
      have hi:=hBOseed i
      positivity
    have hm':0≤((m:ℝ)+1)^4*BMseed₀:=by positivity
    dsimp only [Kpair₀]
    linarith
  have hℓ:∀i,1≤ni i+2:=by intro i;omega
  have hℓmax:∀i,ni i+2≤K:=by intro i;rw [hpadded i];exact long_assigned_padded_length_upper hK3 i
  obtain ⟨η,hη,N₀,hmatch⟩:=long_raw_surviving_matching_all_incidences m K (fun i=>ni i+2)
    hℓ hℓmax Kpair₀ alpha γ hpairpos halpha hγ
  refine ⟨η,hη,max N₀ K,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost hpos hp₂ hk₂ he hdeg hbudgetV hbudgetE t ht tHub htHub hτ hbupper pmin hpmin hbmin hcountErr g₀
  have hn₀:N₀≤n:=(le_trans (le_max_left _ _) (le_max_left _ _)).trans hn
  have hKn:K≤n:=(le_trans (le_max_right _ _) (le_max_left _ _)).trans hn
  have hnpos:0<n:=by have:= (le_max_right (max N₀ K) 1).trans hn;omega
  intro b a p₁ k₁ p₂ k₂ udens q s hLaw μ f pstar BMseed BOseed Wm Wo C ℓ W R Pair Kpair failure Ret ν Prior ε hprior hbudget
  letI : Nonempty (Fin n):=⟨⟨0,hnpos⟩⟩
  have hh:=long_assigned_reference_matching_inputs_witness hnpos F hF Allowed hAllowed K (by omega) m d hm hd θ ρ₀ ρ D
    hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper
    huv hnoshort εHost hpos hp₂ hk₂ he hdeg hbudgetV hbudgetE t ht tHub htHub hK3 hθpos hτ hpadded hbupper
    pmin hpmin hbmin hcountErr hKn alpha halpha halphaMass g₀ Prior ε hprior hbudget
  obtain ⟨z,hz,hPrior,hSpoke,hCount,hM,hO,hload,hMass,hKpair,hW,hCard,hInputs⟩:=hh
  refine ⟨z,hz,hPrior,hSpoke,hCount,hM,hO,hload,hMass,?_⟩
  intro Del δ hDel hmargin herr raw S T e Cand Q fS φ hub test
  obtain ⟨htarget,hdelLoad,hpair,hrange,hmass⟩:=hInputs Del δ hDel hmargin
  have herr':(Fintype.card (Option (Fin K)):ℝ)*(t+C*(δ/(n:ℝ)))+τ≤η:=by
    simpa only [Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using herr
  have hmatchAt:=hmatch n hn₀
  have hdec : referenceWitnessFinDecidable n = instDecidableEqFin n := Subsingleton.elim _ _
  rw [←hdec] at hmatchAt
  have h:=hmatchAt U (LongRetainedHubTest F hF K θ) huv P Del π d raw true true W
    (longAssignedMixedTarget F hF K m θ D p₂ k₂) τ (t+C*(δ/(n:ℝ))) Pair test
    hCard hW htarget hdelLoad herr' hpair hKpair.2 hrange hmass
  obtain ⟨M,hposM,hdis,hrim,hall,hlarge,hlow,hup,hres⟩:=h
  refine ⟨M,hposM,hdis,hrim,hall,hlarge,hlow,hup,?_⟩
  exact hres δ hDel
end Oberwolfach
