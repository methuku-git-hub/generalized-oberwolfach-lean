module

public import Oberwolfach.MarkedActiveCoverDownFromDeepBounds
public import Oberwolfach.MarkedProtectedSeparateGeometryBudgets

@[expose] public section

/-! Construct the active packing from the original parent reference
estimates. The global packing hypotheses are derived on the actual deleted
restriction, using the original fixed weight and one reference accuracy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_cover_down_separate_geometry (gamma pA0:ℝ)
    (hg:0<gamma) (hg1:gamma≤ 1) (hpA0:0<pA0) (hpA01:pA0≤ 1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤ r→         c₀≤ r+5→         ∀ rho omega t p0 betaA aLoA BA:ℝ,
    0<rho→         rho≤ 1→         0<omega→         omega≤ 1→         0<t→         (r+4:ℝ)*t≤ 1→         
    pA0≤ rho*(r+4:ℝ)*t/2→         0<p0→         p0≤ rho*(r+4:ℝ)*t/2→         p0≤ rho*t/2→         p0≤ t→         0<betaA→         0<aLoA→         0<BA→         
    ∃ kappa0 ξ:ℝ,0<kappa0∧ 0<ξ∧ ∀ kappa:ℝ,0<kappa→         kappa≤ kappa0→         
    ∀ alphaInner omegaInner:ℝ,0<alphaInner→      0<omegaInner→      omegaInner≤ 1→      
    ∃ betaExt epsilonExt:ℝ,0<betaExt∧ 0<epsilonExt∧ 
    ∀ ν β aLo B:ℝ,0<ν→     0<β→     β≤ betaExt→     0<aLo→     0≤ B→     
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧ 0<ηEnd∧ 0<ζ∧ 0<ζD∧ 0<pmax∧ pmax≤ 1/8∧ 
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤ 1),p≤ pmax→         ∃ θ:ℝ,0<θ∧ ∀ (Kdeep:ℕ) (etaEmax:ℝ),0<etaEmax→  
    ∃ delta:ℝ,0<delta∧ ∀ x:ℝ,0<x→  x≤ delta→  ∀ d:ℕ,1≤ d→         ∃ N:ℕ,1≤ N∧ 
    ∀ (VP UP W V U Gamma Color:Type) [Fintype VP] [Fintype UP] [LinearOrder VP] [DecidableEq UP]
      [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color],
    N≤ Fintype.card VP→         Fintype.card UP≤ Fintype.card VP→         omega*Fintype.card VP≤ (Fintype.card UP:ℝ)→         
    N≤ Fintype.card W→         omegaInner*Fintype.card (V⊕U)≤ (Fintype.card W:ℝ)→         
    ∀ (fA:V↪oVP) (gA:U↪UP) (PP:SimpleGraph VP) (πP:Equiv.Perm VP) (π:Equiv.Perm V),
    (∀ x,fA (π x)=πP (fA x))→         
    ∀ (T:Finset VP) (Wrem:Finset UP),(∀ x,πP x∈T↔x∈T)→         
    Finset.univ.image fA=Finset.univ\T→         Finset.univ.image gA=Finset.univ\Wrem→         
    (T.card:ℝ)≤ kappa*Fintype.card VP→         (Wrem.card:ℝ)≤ kappa*Fintype.card VP→         
    (∀ x,(1/2+gamma/2)*Fintype.card VP≤ (PP.degree x:ℝ))→         
    (∀ x,|(PP.degree x:ℝ)-2*Fintype.card UP/rho|≤ kappa*Fintype.card VP)→         
    ∀ (qP:UP→         Gamma→         ℝ) (sP:UP→         Color→         ℝ) (aP:Gamma) (cP:Color),
    (∀ u,qP u aP=t)→         (∀ u,sP u cP=(r+4:ℝ)*t)→         
    ∀ (σP:RawMarkedOutcome VP UP Gamma Color) (HP:Bool→         VP→         UP→         Prop),
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card UP/rho;
    MarkedReferenceStatistics PP πP d aP cP DRef kappa kappa gamma pRef kRef ((r+4:ℝ)*t) t σP→         
    MarkedReferenceCutFamilies PP πP d aP cP gamma pRef kRef t σP→         
    MarkedCommonConfigurationsWithSpokes r PP πP d betaA kappa σP HP→         
    MarkedRowsWithSpokes PP πP d (r+12) Finset.univ pRef kRef qP sP aP cP (kappa*Fintype.card VP) σP HP→         
    MarkedIndicesWithSpokes πP d (r+12) Finset.univ qP sP aP cP (kappa*Fintype.card VP) σP HP→         
    (∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤ kappa*Fintype.card UP)→         
    (∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤ kappa*Fintype.card VP)→         
    (Fintype.card VP:ℝ)/2≤ DRef→         DRef≤ 2*Fintype.card VP→         
    ∀ (tauRef:ℝ) (weightRef:(Fin (r+4+1)→         VP)→         ℝ),SuccessorSequenceWeightConditions PP πP (3*d) DRef tauRef aLoA BA weightRef→         
    (let seed:=fun C:MarkedWheel (Prod.fst:VP×VP→         VP) Prod.snd Prod.fst Prod.snd (r+4) πP (3*d)
        (fun (_:VP) (_:UP)=>True) (fun _ _=>True)=>weightRef C.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
      ∀ root,rawMarkedWheelMarginal PP πP d pRef kRef qP sP aP cP root≠0→         
        |typedMarkedPotentialLoad seed (rawMarkedPairRims PP πP d σP) HP root-1|≤ kappa)→         
    let EP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) false
    let KP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) true;
    ∀ (I:Finset VP) (J:Finset UP) (etaE xiDeep:ℝ),0≤ etaE→   0≤ xiDeep→  etaE≤ x→  (4*Kdeep+3*r+50:ℝ)*xiDeep≤ kappa/2→  (1+2/rho)*xiDeep≤ t*omegaInner/32→   
    Wrem⊆J→   
    (T.card:ℝ)≤ xiDeep*Fintype.card VP→   (Wrem.card:ℝ)≤ xiDeep*Fintype.card VP→   
    ∀ ME MD:Finset (MarkedWheel (fun e:EP=>e.val.1) (fun e=>e.val.2)
      (fun e:KP=>e.val.1) (fun e=>e.val.2) (r+4) πP (3*d) (HP false) (HP true)),
    (∀ x,((markedPackingRimGraph ME).degree x:ℝ)≤ 24*etaE*Fintype.card VP)→    
    (∀ x,((Finset.univ.filter (markedPackingSpokes ME x)).card:ℝ)≤ 6*etaE*Fintype.card VP)→    
    (∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes ME x u)).card:ℝ)≤ 3*(r+5)*etaE*Fintype.card VP)→    
    (MD.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\Wrem))=∅→   
    (∀ x∉I,(markedPackingRimGraph MD).degree x≤ 2*Wrem.card+T.card*(4*(Kdeep+4))+2*T.card)→   
    (∀ x∉I,(Finset.univ.filter (markedPackingSpokes MD x)).card≤ Wrem.card+T.card*(Kdeep+4))→   
    (∀ u∉Wrem,(Finset.univ.filter (fun x=>markedPackingSpokes MD x u)).card≤ T.card*(r+5))→   
    ∀ (DR:SimpleGraph VP) (DS:SimpleGraph (VP⊕UP)),
    DR=markedPackingRimGraph ME⊔markedPackingRimGraph MD→   
    DS=markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)→   
    let σ:=rawMarkedRestrictPair fA gA (rawMarkedDeleteRims σP DR.edgeFinset)
    let H:=fun b x u=>markedDeletePhysicalSpokes HP DS b (fA x) (gA u);
    ∀ (f:W↪oV) (ρ:Equiv.Perm W),(∀ x,f (ρ x)=π (f x))→         
    let P:=PP.comap fA;
    let pr:=pRef;let kr:=kRef;let sr:=(r+4:ℝ)*t;
    ∀ (D τweight:ℝ),
    (Fintype.card W:ℝ)/2≤ D→         D≤ 2*Fintype.card W→         
    ∀ weight:(Fin (r+4+1)→         W)→         ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight→         
    ∀ Zinner:Finset U,
    (∀ u v,¬(HP false v u∧ HP true v u))→    
    (∀ u v z,HP false v u→    HP true z u→    v≠πP z)→    
    let Q:=fun u=>qP (gA u)
    let S:=fun u=>sP (gA u)
    let g:=aP;let c:=cP
    let X:=Finset.univ.image f;
    X.image fA=I\T→   Zinner.image gA=J\Wrem→   
    MarkedRowsWithSpokes (PP.comap (f.comp fA)) ρ d 1 Finset.univ pr kr Q S g c ((t/4)*Fintype.card W)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→    
    MarkedLocalConfigurationsWithSpokes r (PP.comap (f.comp fA)) ρ d Finset.univ (2*β) (2*β)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→    
    MarkedLocalSpokeLoadsWithSpokes (PP.comap (f.comp fA)) ρ d (r+4) D pr kr sr weight (η/2)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→    
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    ∀ errR0 errI0:ℝ,0≤ errR0→    0≤ errI0→    
    let errR:=errR0+(r+12:ℕ)*(24*etaE*Fintype.card VP+3*(r+5)*etaE*Fintype.card VP)
    let errI:=errI0+(r+12:ℕ)*(6*etaE*Fintype.card VP);

    errR0≤ x*Fintype.card VP→  errI0≤ x*Fintype.card VP→  
    omegaInner*Fintype.card (V⊕U)≤ (Zinner.card:ℝ)→      

    MarkedRowsWithSpokes PP πP d (r+12) (X.image fA) pr kr qP sP g c errR0 σP HP→    
    MarkedIndicesWithSpokes πP d (r+12) (Zinner.image gA) qP sP g c errI0 σP HP→    

    ∀ errParent:ℝ,0≤ errParent→   
    (∀ v,|((PP.neighborFinset v∩I).card:ℝ)-2*J.card/rho|≤ errParent)→   
    (∀ v,(1/2+2*alphaInner)*I.card≤ ((PP.neighborFinset v∩I).card:ℝ))→   
    (T.card:ℝ)≤ alphaInner*I.card→   
    let deltaParent:=errParent+T.card+2*Wrem.card/rho;
    errParent≤ x*Fintype.card VP→  
    let pA:=rho*(r+4:ℝ)*t/2
    let DA:=2*Fintype.card U/rho;
    ( (ordinaryInnerVertices X Zinner).card:ℝ)≤ ξ*Fintype.card V →         
    (∀ x,π x∈X↔x∈X) →         
    ∀ (innerOrder mu errInner errDeep:ℝ),
    (Fintype.card VP:ℝ)/2≤ Fintype.card V→        innerOrder≤ Fintype.card VP→        0≤ mu→        
    errInner≤ x*Fintype.card VP→  errDeep≤ x*Fintype.card VP→  mu≤ x→  
    (∀ (z:V⊕U) (i:Fin 4),
      |markedFiniteBalance tail head ktail khead (H true) Finset.univ
        (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) z i|
        ≤ errDeep+((r+4:ℕ)+2)*(mu*innerOrder)∧ 
      |markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ
        (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) X Zinner z i|
        ≤ errInner+errDeep+((r+4:ℕ)+2)*(4*(24*etaE*Fintype.card VP)+3*(r+5)*etaE*Fintype.card VP))→        
    MarkedOutsideBalance tail head ktail khead (H true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) X Zinner→         
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
       (∀ W∈M,∀ W'∈M,W≠W'→         Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧ 
       (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤ ν*Fintype.card (V⊕U))∧ 
       (∀ v∈X,((Zinner.filter (markedPackingSpokes M v)).card:ℝ)≤ ν*Fintype.card (V⊕U))∧ 
       (∀ u∈Zinner,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤ ν*Fintype.card (V⊕U))∧ 
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2))\M.biUnion markedWheelSpokePairs
        (∀ a∈A',Sum.elim tail ktail a∈X∧ Sum.elim head khead a∈X)∧ 
          (∀ s∈S',s.1∈X∧ s.2∈Zinner)∧ 
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources) :=by
  obtain ⟨c₀,hcover⟩:=marked_active_cover_down_from_deep_bounds gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  have hp01:p0≤ 1/2:=by
    have hh:=mul_le_mul_of_nonneg_left ht1 hrho.le
    nlinarith only [hh,hrho1,hpr]
  obtain ⟨kappa0,ξ,hkappa0,hξ,hcover⟩:=hcover r hr hrc rho omega t p0 betaA aLoA BA
    hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  refine ⟨kappa0,ξ,hkappa0,hξ,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩:=hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,?_⟩
  intro ν β aLo B hν hβ hBetaSmall haLo hB
  let a:=t*omegaInner/2
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩:=hcover ν β aLo B
    hν hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,hcover⟩:=hcover p hp hp1 hpp
  refine ⟨θ,hθ,?_⟩
  intro Kdeep etaEmax hEtaEmax
  obtain ⟨delta,hdelta,hbudget⟩:=marked_protected_inner_budget_scale r Kdeep (r+12) omegaInner kappa rho t ζD epsilonExt
    ηEnd a θ etaEmax hOmega hkappa hrho ht hζD hEpsilonExt hηEnd (by dsimp [a];positivity) hθ hEtaEmax
  refine ⟨delta,hdelta,?_⟩
  intro x hx hxdelta
  obtain ⟨bGlobal,bR,bS,bExt,bEnd,bGap,bBalance,bMu,bEta,bMax,bOmega,bKappa⟩:=hbudget x hx.le hxdelta

  intro d hd
  obtain ⟨NC,hNC,hcover⟩:=hcover d hd
  obtain ⟨NE,hNE,hException⟩:=marked_protected_inner_exception_order (t/2) omegaInner (by positivity) hOmega d
  refine ⟨max NC NE,hNC.trans (le_max_left _ _),?_⟩
  intro VP UP W V U Gamma Color _ _ _ _ _ _ _ _ _ _ _ _ hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    pRef kRef DRef hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    EP KP I J etaE xiDeep heE hxiDeep hEtaSmall hXiScale hDeepGap hWremJ hTdeep hWdeep
    ME MD hMER hMEV hMEU hMDstar hMDR hMDV hMDU DR DS hDR hDS σ H
    f ρ hf P pr kr sr D τweight hDlo hDhi weight hw Zinner hdtypesP hsepP Q S g c X
    hXimage hZimage hrows0 hconfigs0 hload0 E K tail head ktail khead
    errR0 errI0 heR0 heI0 errR errI hErrR hErrI hZlow hrowEnd0 hidxEnd0
    errParent heP hNearP hMinP hTinner deltaParent hErrParent pA DA hinnerSize hX
    innerOrder mu errInner errDeep hVhalf hInnerOrder hmu hErrInner0 hErrDeep0 hMuSmall hfinite hdiv
  have hn0:0≤ (Fintype.card VP:ℝ):=Nat.cast_nonneg _
  have hAmbientHalf:(Fintype.card VP:ℝ)/2≤ Fintype.card (V⊕U):=by
    have hh:(Fintype.card V:ℝ)≤ Fintype.card (V⊕U):=by
      simpa only [Fintype.card_sum,Nat.cast_add] using
        (le_add_of_nonneg_right (Nat.cast_nonneg (α:=ℝ) (Fintype.card U)) : (Fintype.card V:ℝ)≤ Fintype.card V+Fintype.card U)
    exact hVhalf.trans hh
  have hWparent:(omegaInner/2)*Fintype.card VP≤ (Fintype.card W:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_left hAmbientHalf hOmega.le
    nlinarith only [hh,hWlow]
  have hZparent:omegaInner*Fintype.card VP/2≤ (Zinner.card:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_left hAmbientHalf hOmega.le
    nlinarith only [hh,hZlow]
  have hWparent':omegaInner*Fintype.card VP/2≤ (Fintype.card W:ℝ):=by nlinarith only [hWparent]
  obtain ⟨hExtR0,hExtI,heRsmall,heIsmall,hSmallR,hSmallI⟩:=marked_protected_inner_error_budget_separate_geometry r (r+12)
    rho omegaInner t epsilonExt ηEnd a x (Fintype.card VP) (Fintype.card (V⊕U)) (Fintype.card W) Zinner.card
    hrho hOmega.le ht.le hEpsilonExt.le hηEnd.le (by dsimp [a];positivity) hx.le hn0 hAmbientHalf
    hWparent' hZparent bExt bEnd bGap xiDeep hDeepGap etaE errR0 errI0 errParent T.card Wrem.card (6*(d:ℝ)+1)
    heE hEtaSmall hErrR hErrI hErrParent hTdeep hWdeep
    (by have hh:=hException _ ((le_max_right _ _).trans hnP);nlinarith only [hh])
  have hXcard:X.card=Fintype.card W:=by
    dsimp [X];rw [Finset.card_image_of_injective _ f.injective,Finset.card_univ]
  have hExtR:errR≤ epsilonExt*X.card:=by rw [hXcard];exact hExtR0
  have hEscale:(4*Kdeep+3*r+50:ℝ)*etaE≤ kappa/2:=
    (mul_le_mul_of_nonneg_left hEtaSmall (by positivity)).trans bGlobal
  have hRbudget:24*etaE≤ ζD*(omegaInner/2):=
    (mul_le_mul_of_nonneg_left hEtaSmall (by norm_num)).trans bR
  have hSbudget:3*(r+5:ℝ)*etaE≤ ζD*(omegaInner/2):=
    (mul_le_mul_of_nonneg_left hEtaSmall (by positivity)).trans bS
  have hscaleBalance:=mul_le_mul_of_nonneg_right bBalance hn0
  have hErrInner:errInner≤ θ*Fintype.card VP/8:=by nlinarith only [hErrInner0,hscaleBalance]
  have hErrDeep:errDeep≤ θ*Fintype.card VP/8:=by nlinarith only [hErrDeep0,hscaleBalance]
  have hMuBound:(r+6:ℝ)*mu≤ θ/8:=(mul_le_mul_of_nonneg_left hMuSmall (by positivity)).trans bMu
  have hEtaBound:(r+6:ℝ)*(96+3*(r+5:ℝ))*etaE≤ θ/4:=
    (mul_le_mul_of_nonneg_left hEtaSmall (by positivity)).trans bEta
  exact hcover VP UP W V U Gamma Color ((le_max_left _ _).trans hnP) hUP hUPlow
    ((le_max_left _ _).trans hnW) hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    I J Kdeep etaE xiDeep heE hxiDeep hWremJ hTdeep hWdeep hEscale hXiScale
    ME MD hMER hMEV hMEU hMDstar hMDR hMDV hMDU DR DS hDR hDS
    f ρ hf D τweight hDlo hDhi weight hw Zinner hdtypesP hsepP hXimage hZimage
    (omegaInner/2) hWparent hRbudget hSbudget hrows0 hconfigs0 hload0
    errR0 errI0 heR0 heI0 heRsmall heIsmall hExtR hExtI hZlow hrowEnd0 hidxEnd0
    errParent heP hNearP hMinP hTinner hSmallR hSmallI hinnerSize hX
    innerOrder mu errInner errDeep hVhalf hInnerOrder hmu hErrInner hErrDeep hMuBound hEtaBound hfinite hdiv

end Oberwolfach
