module

public import Oberwolfach.MarkedActiveCoverDownLocalExtensions
public import Oberwolfach.MarkedEndpointClassSizes

@[expose] public section

/-! Construct the active packing from the original parent reference
estimates. The global packing hypotheses are derived on the actual deleted
restriction, using the original fixed weight and one reference accuracy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 60000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_cover_down_endpoint_inputs (gamma pA0:ℝ)
    (hg:0<gamma) (hg1:gamma≤1) (hpA0:0<pA0) (hpA01:pA0≤1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤r→     c₀≤r+5→     ∀ rho omega t p0 betaA aLoA BA:ℝ,
    0<rho→     rho≤1→     0<omega→     omega≤1→     0<t→     (r+4:ℝ)*t≤1→     
    pA0≤rho*(r+4:ℝ)*t/2→     0<p0→     p0≤rho*(r+4:ℝ)*t/2→     p0≤rho*t/2→     p0≤t→     0<betaA→     0<aLoA→     0<BA→     
    ∃ kappa0 ξ:ℝ,0<kappa0∧0<ξ∧∀ kappa:ℝ,0<kappa→     kappa≤kappa0→     
    ∀ alphaInner omegaInner:ℝ,0<alphaInner→  0<omegaInner→  omegaInner≤1→  
    ∃ betaExt epsilonExt:ℝ,0<betaExt∧0<epsilonExt∧
    let a:=t*omegaInner/2;let gap:=t*omegaInner/4;
    ∀ ν β aLo B:ℝ,0<ν→ 0<β→ β≤betaExt→ 0<aLo→ 0≤B→ 
    ∃ η ηEnd ζ pmax:ℝ,0<η∧0<ηEnd∧0<ζ∧0<pmax∧pmax≤1/8∧
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤1),p≤pmax→     ∃ θ:ℝ,0<θ∧∀ d:ℕ,1≤d→     ∃ N:ℕ,1≤N∧
    ∀ (VP UP W V U Gamma Color:Type) [Fintype VP] [Fintype UP] [LinearOrder VP] [DecidableEq UP]
      [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color],
    N≤Fintype.card VP→     Fintype.card UP≤Fintype.card VP→     omega*Fintype.card VP≤(Fintype.card UP:ℝ)→     
    N≤Fintype.card W→     omegaInner*Fintype.card (V⊕U)≤(Fintype.card W:ℝ)→     
    ∀ (fA:V↪oVP) (gA:U↪UP) (PP:SimpleGraph VP) (πP:Equiv.Perm VP) (π:Equiv.Perm V),
    (∀ x,fA (π x)=πP (fA x))→     
    ∀ (T:Finset VP) (Wrem:Finset UP),(∀ x,πP x∈T↔x∈T)→     
    Finset.univ.image fA=Finset.univ\T→     Finset.univ.image gA=Finset.univ\Wrem→     
    (T.card:ℝ)≤kappa*Fintype.card VP→     (Wrem.card:ℝ)≤kappa*Fintype.card VP→     
    (∀ x,(1/2+gamma/2)*Fintype.card VP≤(PP.degree x:ℝ))→     
    (∀ x,|(PP.degree x:ℝ)-2*Fintype.card UP/rho|≤kappa*Fintype.card VP)→     
    ∀ (qP:UP→     Gamma→     ℝ) (sP:UP→     Color→     ℝ) (aP:Gamma) (cP:Color),
    (∀ u,qP u aP=t)→     (∀ u,sP u cP=(r+4:ℝ)*t)→     
    ∀ (σP:RawMarkedOutcome VP UP Gamma Color) (HP:Bool→     VP→     UP→     Prop),
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card UP/rho;
    MarkedReferenceStatistics PP πP d aP cP DRef kappa kappa gamma pRef kRef ((r+4:ℝ)*t) t σP→     
    MarkedReferenceCutFamilies PP πP d aP cP gamma pRef kRef t σP→     
    MarkedCommonConfigurationsWithSpokes r PP πP d betaA kappa σP HP→     
    MarkedRowsWithSpokes PP πP d (r+12) Finset.univ pRef kRef qP sP aP cP (kappa*Fintype.card VP) σP HP→     
    MarkedIndicesWithSpokes πP d (r+12) Finset.univ qP sP aP cP (kappa*Fintype.card VP) σP HP→     
    (∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤kappa*Fintype.card UP)→     
    (∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤kappa*Fintype.card VP)→     
    (Fintype.card VP:ℝ)/2≤DRef→     DRef≤2*Fintype.card VP→     
    ∀ (tauRef:ℝ) (weightRef:(Fin (r+4+1)→     VP)→     ℝ),SuccessorSequenceWeightConditions PP πP (3*d) DRef tauRef aLoA BA weightRef→     
    (let seed:=fun C:MarkedWheel (Prod.fst:VP×VP→     VP) Prod.snd Prod.fst Prod.snd (r+4) πP (3*d)
        (fun (_:VP) (_:UP)=>True) (fun _ _=>True)=>weightRef C.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
      ∀ root,rawMarkedWheelMarginal PP πP d pRef kRef qP sP aP cP root≠0→     
        |typedMarkedPotentialLoad seed (rawMarkedPairRims PP πP d σP) HP root-1|≤kappa)→     
    ∀ (DR:SimpleGraph VP) (DS:SimpleGraph (VP⊕UP)),
    (∀ x,((DR.comap fA).degree x:ℝ)≤kappa*Fintype.card VP)→     
    (∀ x,((DS.comap (Sum.map fA gA)).degree (Sum.inl x):ℝ)≤kappa*Fintype.card VP)→     
    (∀ u,((DS.comap (Sum.map fA gA)).degree (Sum.inr u):ℝ)≤kappa*Fintype.card VP)→     
    let σ:=rawMarkedRestrictPair fA gA (rawMarkedDeleteRims σP DR.edgeFinset)
    let H:=fun b x u=>markedDeletePhysicalSpokes HP DS b (fA x) (gA u);
    ∀ (f:W↪oV) (ρ:Equiv.Perm W),(∀ x,f (ρ x)=π (f x))→     
    let P:=PP.comap fA;
    let pr:=pRef;let kr:=kRef;let sr:=(r+4:ℝ)*t;
    ∀ (D τweight:ℝ),
    (Fintype.card W:ℝ)/2≤D→     D≤2*Fintype.card W→     
    ∀ weight:(Fin (r+4+1)→     W)→     ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight→     
    ∀ Zinner:Finset U,
    (∀ u v,¬(H false v u∧H true v u))→     
    (∀ u v z,H false v u→     H true z u→     v≠π z)→     
    let Q:=fun u=>qP (gA u)
    let S:=fun u=>sP (gA u)
    let g:=aP;let c:=cP;
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ pr kr Q S g c ((t/2)*Fintype.card W)
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→     
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ β β
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→     
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D pr kr sr weight η
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→     
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let X:=Finset.univ.image f;
    ∀ errR errI:ℝ,0≤errR→  0≤errI→  
      2*errR≤ηEnd*(a*Fintype.card (V⊕U))→  2*errI≤ηEnd*(a*Fintype.card (V⊕U))→  
    errR≤epsilonExt*X.card→  errI≤epsilonExt*Zinner.card→  
    omegaInner*Fintype.card (V⊕U)≤(Zinner.card:ℝ)→  
    (∀ v,(1/2+alphaInner)*X.card≤((X∩P.neighborFinset v).card:ℝ))→  
    MarkedRowsWithSpokes P π d (r+12) X pr kr Q S g c errR σ H→  
    MarkedIndicesWithSpokes π d (r+12) Zinner Q S g c errI σ H→  
    ∀ deltaParent:ℝ,0≤deltaParent→ 
    (∀ v,|((P.neighborFinset v∩X).card:ℝ)-2*Zinner.card/rho|≤deltaParent)→ 
    errR+(6*(d:ℝ)+1)+deltaParent≤t*omegaInner*Fintype.card (V⊕U)/4→ 
    errI≤t*omegaInner*Fintype.card (V⊕U)/4→ 
    let pA:=rho*(r+4:ℝ)*t/2
    let DA:=2*Fintype.card U/rho;
    ( (ordinaryInnerVertices X Zinner).card:ℝ)≤ξ*Fintype.card V →     
    (∀ x,π x∈X↔x∈X) →     
    ∀ (innerOrder mu etaE errInner errDeep:ℝ),
    (Fintype.card VP:ℝ)/2≤Fintype.card V→    innerOrder≤Fintype.card VP→    0≤mu→    
    errInner≤θ*Fintype.card VP/8→    errDeep≤θ*Fintype.card VP/8→    
    (r+6:ℝ)*mu≤θ/8→    (r+6:ℝ)*(96+3*(r+5:ℝ))*etaE≤θ/4→    
    (∀ (z:V⊕U) (i:Fin 4),
      |markedFiniteBalance tail head ktail khead (H true) Finset.univ
        (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) z i|
        ≤errDeep+((r+4:ℕ)+2)*(mu*innerOrder)∧
      |markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ
        (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) X Zinner z i|
        ≤errInner+errDeep+((r+4:ℕ)+2)*(4*(24*etaE*Fintype.card VP)+3*(r+5)*etaE*Fintype.card VP))→    
    MarkedOutsideBalance tail head ktail khead (H true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) X Zinner→     
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
       (∀ W∈M,∀ W'∈M,W≠W'→     Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
       (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ v∈X,((Zinner.filter (markedPackingSpokes M v)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ u∈Zinner,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2))\M.biUnion markedWheelSpokePairs
        (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
          (∀ s∈S',s.1∈X∧s.2∈Zinner)∧
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources) :=by
  obtain ⟨c₀,hcover⟩:=marked_active_cover_down_local_extensions gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  have hp01:p0≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_left ht1 hrho.le
    nlinarith only [hh,hrho1,hpr]
  obtain ⟨kappa0,ξ,hkappa0,hξ,hcover⟩:=hcover r hr hrc rho omega t p0 betaA aLoA BA
    hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  refine ⟨kappa0,ξ,hkappa0,hξ,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩:=hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,?_⟩
  intro a gap ν β aLo B hν hβ hBetaSmall haLo hB
  have ha:0<a:=by dsimp [a];positivity
  have hgap:0<gap:=by dsimp [gap];positivity
  have htmax:t≤1:=by
    have hn:=Nat.cast_nonneg (α:=ℝ) r
    nlinarith only [ht1,mul_nonneg hn ht.le,ht.le]
  have ha1:a≤1:=by
    have hh:=mul_le_mul htmax hOmega1 hOmega.le (by norm_num : (0:ℝ)≤1)
    dsimp [a];linarith only [hh]
  obtain ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,hcover⟩:=hcover ν β aLo B a gap
    hν hβ hBetaSmall haLo hB ha ha1 hgap
  refine ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,hcover⟩:=hcover p hp hp1 hpp
  refine ⟨θ,hθ,?_⟩
  intro d hd
  obtain ⟨N,hN,hcover⟩:=hcover d hd
  refine ⟨N,hN,?_⟩
  intro VP UP W V U Gamma Color _ _ _ _ _ _ _ _ _ _ _ _ hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    pRef kRef DRef hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    DR DS hrimD hrowD hcolD σ H
    f ρ hf P pr kr sr D τweight hDlo hDhi weight hw Zinner hdtypes hsep
    Q S g c hrows hconfigs hload E K tail head ktail khead X
    errR errI heR heI heRsmall heIsmall hExtR hExtI hZlow hParentInner hrowEnd hidxEnd
    deltaParent hDeltaParent hNearInner hSmallR hSmallI pA DA hinnerSize hX
    innerOrder mu etaE errInner errDeep hVhalf hInnerOrder hmu hErrInner hErrDeep hMuBound hEtaBound hfinite hdiv
  have hrc:(((r+5:ℕ):ℝ)-1)=(r+4:ℝ):=by push_cast;ring
  have hkrform:kr=rho*t/2:=by dsimp [kr,kRef,pRef];field_simp <;> ring
  have hQ:∀ u∈Zinner,Q u g=t:=fun u _=>hqP (gA u)
  have hS:∀ u∈Zinner,S u c=(((r+5:ℕ):ℝ)-1)*t:=by
    intro u hu
    rw [hrc]
    exact hsP (gA u)
  have hrowEnd':MarkedRowsWithSpokes P π d (r+12) X (rho*((((r+5:ℕ):ℝ)-1)*t)/2)
      (rho*t/2) Q S g c errR σ H:=by
    rw [hrc]
    simpa only [hkrform,pr,pRef,mul_assoc] using hrowEnd
  obtain ⟨hL,hS',hgap'⟩:=marked_endpoint_class_sizes P π d (r+12) (by omega) X Zinner hX
    (Fintype.card (V⊕U)) omegaInner t rho hOmega ht hrho hrho1 (r+5) (by omega)
    (by simpa only [hrc] using ht1) hZlow Q S g c hQ hS errR errI deltaParent (t*omegaInner/8)
    heR heI hDeltaParent hNearInner hSmallR hSmallI le_rfl σ H hrowEnd' hidxEnd
  have hgapParent:∀ v∉X,((markedEndpointLabels P π d X (true,false,v) σ).card:ℝ)+
      gap*Fintype.card (V⊕U)≤(Zinner.filter (H false v)).card:=by
    intro v hv
    convert hgap' v using 1 <;> dsimp [gap] <;> ring
  exact hcover VP UP W V U Gamma Color hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    DR DS hrimD hrowD hcolD f ρ hf D τweight hDlo hDhi weight hw Zinner hdtypes hsep hrows hconfigs hload
    errR errI heR heI heRsmall heIsmall hExtR hExtI hZlow hParentInner hrowEnd hidxEnd
    (fun v _ j=>⟨hL (markedEndpointFiveRimType j) (markedEndpointFiveIncoming j) v,
      hS' (markedEndpointFiveRootSpokeType j) v⟩) hgapParent
    hinnerSize hX innerOrder mu etaE errInner errDeep hVhalf hInnerOrder hmu hErrInner hErrDeep hMuBound hEtaBound hfinite hdiv

end Oberwolfach
