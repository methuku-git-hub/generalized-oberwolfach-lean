module

public import Oberwolfach.MarkedProtectedCoverDownSeparatedTolerancesUniform
public import Oberwolfach.MarkedProtectedCoverDownSeparatedTolerances
public import Oberwolfach.MarkedConstructedDeepCanonicalEstimates
public import Oberwolfach.MarkedFiniteCorrectionIncidence
public import Oberwolfach.MarkedFiniteInnerGraphSupport
public import Oberwolfach.MarkedProtectedFinalMargins

@[expose] public section

/-! The protected cover-down theorem in an order usable for iteration.
The analytic input tolerance is chosen before the arbitrary requested star
loss. The inner correction is then smaller than that loss; only inner-root
imbalance needs the still smaller correction tolerance. All packings are
constructed from the displayed graph inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_protected_cover_down_iterable_uniform_densities (gamma pA0:ℝ)
    (hg:0< gamma) (hg1:gamma≤   1) (hpA0:0< pA0) (hpA01:pA0≤   1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤r→c₀≤r+5→∀ rho₀ omega₀ t₀ p0 betaA aLoA BA:ℝ,
    0<rho₀ → rho₀≤1 → 0<omega₀ → 0<t₀ → t₀≤1 → 0<p0 → p0≤1/2 → 0<betaA → 0<aLoA → 0<BA →
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa→           kappa≤   kappa0→           
    ∀ alphaInner omegaInner:ℝ,0< alphaInner→        0< omegaInner→        omegaInner≤   1→        
    ∃ betaExt epsilonExt:ℝ,0< betaExt∧   0< epsilonExt∧   
    ∀ gammaLoss iota β aLo B:ℝ,0< gammaLoss→  0< iota→       0<β→       β≤   betaExt→       0< aLo→       0≤   B→       
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ) (hp:0< p) (hp1:p≤   1),p≤   pmax→           ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x→   x≤   delta→   
    ∀ sigmaLoss:ℝ,0< sigmaLoss→ ∀ omegaI hIcut deltaI:ℝ,0< omegaI→   0< hIcut→   0< deltaI→   deltaI<1/4→   
    ∃ etaBal:ℝ,0< etaBal∧   ∃ NI:ℕ,∀ d:ℕ,1≤   d→           ∃ N:ℕ,1≤   N∧   
    ∀ rho omega t:ℝ,rho₀≤rho → rho≤1 → omega₀≤omega → omega≤1 → t₀≤t → (r+4:ℝ)*t≤1 →
    pA0≤rho*(r+4:ℝ)*t/2 → p0≤rho*(r+4:ℝ)*t/2 → p0≤rho*t/2 → p0≤t →
    ∀ (VP UP W V U Gamma Color:Type) [Fintype VP] [Fintype UP] [LinearOrder VP] [DecidableEq UP]
      [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color],
    N≤   Fintype.card VP→           Fintype.card UP≤   Fintype.card VP→           omega*Fintype.card VP≤   (Fintype.card UP:ℝ)→           
    N≤   Fintype.card W→           omegaInner*Fintype.card (V⊕U)≤   (Fintype.card W:ℝ)→           
    ∀ (fA:V↪oVP) (gA:U↪UP) (PP:SimpleGraph VP) (πP:Equiv.Perm VP) (π:Equiv.Perm V),
    (∀ x,fA (π x)=πP (fA x))→           
    ∀ (T:Finset VP) (Wrem:Finset UP),(∀ x,πP x∈T↔x∈T)→           
    Finset.univ.image fA=Finset.univ\T→           Finset.univ.image gA=Finset.univ\Wrem→           
    (T.card:ℝ)≤   kappa*Fintype.card VP→           (Wrem.card:ℝ)≤   kappa*Fintype.card VP→           
    (∀ x,(1/2+gamma/2)*Fintype.card VP≤   (PP.degree x:ℝ))→           
    (∀ x,|(PP.degree x:ℝ)-2*Fintype.card UP/rho|≤   kappa*Fintype.card VP)→           
    ∀ (qP:UP→           Gamma→           ℝ) (sP:UP→           Color→           ℝ) (aP:Gamma) (cP:Color),
    (∀ u,qP u aP=t)→           (∀ u,sP u cP=(r+4:ℝ)*t)→           
    ∀ (σP:RawMarkedOutcome VP UP Gamma Color) (HP:Bool→           VP→           UP→           Prop),
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card UP/rho;
    MarkedReferenceStatistics PP πP d aP cP DRef kappa kappa gamma pRef kRef ((r+4:ℝ)*t) t σP→           
    MarkedReferenceCutFamilies PP πP d aP cP gamma pRef kRef t σP→           
    MarkedCommonConfigurationsWithSpokes r PP πP d betaA kappa σP HP→           
    MarkedRowsWithSpokes PP πP d (r+12) Finset.univ pRef kRef qP sP aP cP (kappa*Fintype.card VP) σP HP→           
    MarkedIndicesWithSpokes πP d (r+12) Finset.univ qP sP aP cP (kappa*Fintype.card VP) σP HP→           
    (∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤   kappa*Fintype.card UP)→           
    (∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤   kappa*Fintype.card VP)→           
    (Fintype.card VP:ℝ)/2≤   DRef→           DRef≤   2*Fintype.card VP→           
    ∀ (tauRef:ℝ) (weightRef:(Fin (r+4+1)→           VP)→           ℝ),SuccessorSequenceWeightConditions PP πP (3*d) DRef tauRef aLoA BA weightRef→           
    (let seed:=fun C:MarkedWheel (Prod.fst:VP×VP→           VP) Prod.snd Prod.fst Prod.snd (r+4) πP (3*d)
        (fun (_:VP) (_:UP)=>True) (fun _ _=>True)=>weightRef C.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
      ∀ root,rawMarkedWheelMarginal PP πP d pRef kRef qP sP aP cP root≠0→           
        |typedMarkedPotentialLoad seed (rawMarkedPairRims PP πP d σP) HP root-1|≤   kappa)→           
    let EP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) false
    let KP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) true;
    MarkedLocalConfigurationsWithSpokes r PP πP d Finset.univ (2*(min betaA (t/4))) (2*(min betaA (t/4))) σP HP→   
    MarkedLocalSpokeLoadsWithSpokes PP πP d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weightRef (thetaDeep/2) σP HP→   
    ∀ (I:Finset VP) (J:Finset UP) (xiDeep:ℝ),0≤  xiDeep→  
    (4*Kgeom+3*r+50:ℝ)*xiDeep≤  kappa/2→  (1+2/rho)*xiDeep≤  t*omegaInner/32→  T⊆I→    Wrem⊆J→   
    (∀ v,πP v∈I↔v∈I)→   
    (I.card:ℝ)≤   ξ*Fintype.card VP→   (J.card:ℝ)≤   ξ*Fintype.card VP→   
    NI≤   I.card→   omegaI*I.card≤   J.card→   J.card≤   I.card→   
    (T.card:ℝ)≤   hIcut*I.card→   (Wrem.card:ℝ)≤   hIcut*J.card→   
    (T.card:ℝ)≤   xiDeep*Fintype.card VP→   (Wrem.card:ℝ)≤   xiDeep*Fintype.card VP→   
    ∀ (f:W↪oV) (ρ:Equiv.Perm W),(∀ x,f (ρ x)=π (f x))→           
    let P:=PP.comap fA;
    let pr:=pRef;let kr:=kRef;let sr:=(r+4:ℝ)*t;
    ∀ (D τweight:ℝ),
    (Fintype.card W:ℝ)/2≤   D→           D≤   2*Fintype.card W→           
    ∀ weight:(Fin (r+4+1)→           W)→           ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight→           
    ∀ Zinner:Finset U,
    (∀ u v,¬(HP false v u∧   HP true v u))→      
    (∀ u v z,HP false v u→      HP true z u→      v≠πP z)→      
    let Q:=fun u=>qP (gA u)
    let S:=fun u=>sP (gA u)
    let g:=aP;let c:=cP
    let X:=Finset.univ.image f;
    X.image fA=I\T→     Zinner.image gA=J\Wrem→     
    MarkedRowsWithSpokes (PP.comap (f.comp fA)) ρ d 1 Finset.univ pr kr Q S g c ((t/4)*Fintype.card W)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→      
    MarkedLocalConfigurationsWithSpokes r (PP.comap (f.comp fA)) ρ d Finset.univ (2*β) (2*β)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→      
    MarkedLocalSpokeLoadsWithSpokes (PP.comap (f.comp fA)) ρ d (r+4) D pr kr sr weight (η/2)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→      
    ∀ errR0 errI0:ℝ,0≤   errR0→      0≤   errI0→      

    errR0≤   x*Fintype.card VP→    errI0≤   x*Fintype.card VP→    
    omegaInner*Fintype.card (V⊕U)≤   (Zinner.card:ℝ)→        

    MarkedRowsWithSpokes PP πP d (r+12) (X.image fA) pr kr qP sP g c errR0 σP HP→      
    MarkedIndicesWithSpokes πP d (r+12) (Zinner.image gA) qP sP g c errI0 σP HP→      

    ∀ errParent:ℝ,0≤   errParent→     
    (∀ v,|((PP.neighborFinset v∩I).card:ℝ)-2*J.card/rho|≤   errParent)→     
    (∀ v,(1/2+2*alphaInner)*I.card≤   ((PP.neighborFinset v∩I).card:ℝ))→     
    (T.card:ℝ)≤   alphaInner*I.card→     
    errParent≤   x*Fintype.card VP→    
    let pA:=rho*(r+4:ℝ)*t/2
    let DA:=2*Fintype.card U/rho;
    ( (ordinaryInnerVertices X Zinner).card:ℝ)≤   ξ*Fintype.card V →           
    (∀ x,π x∈X↔x∈X) →           
    iota*Fintype.card VP≤  I.card→ 
    (Fintype.card VP:ℝ)/2≤  Fintype.card V→   
    ∀ errInner errDeep:ℝ,0≤   errDeep→   errInner≤   x*Fintype.card VP→   errDeep≤   x*Fintype.card VP→   
    let tailP:=fun e:EP=>e.val.1
    let headP:=fun e:EP=>e.val.2
    let ktailP:=fun e:KP=>e.val.1
    let kheadP:=fun e:KP=>e.val.2
    let SP:=Finset.univ.filter (fun z:VP×UP=>HP false z.1 z.2∨HP true z.1 z.2)
    let EI:={e:EP // tailP e∈I∧   headP e∈I}
    let KI:={e:KP // ktailP e∈I∧   kheadP e∈I}
    let tI:=fun e:EI=>(⟨tailP e.val,e.property.1⟩:I)
    let hI':=fun e:EI=>(⟨headP e.val,e.property.2⟩:I)
    let ktI:=fun e:KI=>(⟨ktailP e.val,e.property.1⟩:I)
    let khI:=fun e:KI=>(⟨kheadP e.val,e.property.2⟩:I)
    let H0Inner:=fun v:I=>fun u:J=>HP false v.val u.val
    let HKInner:=fun v:I=>fun u:J=>HP true v.val u.val
    (∀ v,|occurrenceDegree (Sum.elim tI ktI) v-
      (∑ u,if H0Inner v u then (1:ℝ) else 0)-(∑ u,if HKInner v u then (1:ℝ) else 0)|≤   etaBal*I.card)→   
    (∀ v,|occurrenceDegree (Sum.elim hI' khI) v-
      (∑ u,if H0Inner v u then (1:ℝ) else 0)-(∑ u,if HKInner v u then (1:ℝ) else 0)|≤   etaBal*I.card)→   
    (∀ v,|occurrenceDegree khI v-(∑ u,if HKInner v u then (1:ℝ) else 0)|≤   etaBal*I.card)→   
    (∀ u,|(∑ v,if H0Inner v u then (1:ℝ) else 0)-(r+4:ℕ)*(∑ v,if HKInner v u then (1:ℝ) else 0)|≤   etaBal*I.card)→   
    BipartiteLargeCut (occurrenceMultiplicity tI hI') deltaI (2*hIcut)→   
    BipartiteLargeCut (occurrenceMultiplicity ktI khI) deltaI (2*hIcut)→   
    BipartiteLargeCut (relationMultiplicity H0Inner) deltaI (2*hIcut)→   
    BipartiteLargeCut (relationMultiplicity HKInner) deltaI (2*hIcut)→   
    MarkedRemainderDivisible tailP headP ktailP kheadP (HP true) Finset.univ SP (r+4)→   
    (∀ z i,|markedFiniteDomainBalance tailP headP ktailP kheadP (HP true) Finset.univ SP (r+4) I J z i|≤   errInner)→   
    (∀ z i,|markedFiniteDomainBalance tailP headP ktailP kheadP (HP true) Finset.univ SP (r+4) T Wrem z i|≤   errDeep)→   
    ∃ E₀:Finset (Finset VP⊕(VP×UP)),
    ∃ N:Finset (MarkedWheel (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2)
      (r+4) πP (3*d) (HP false) (HP true)),
      (∀ Y∈N,∀ Y'∈N,Y≠Y'→   Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Y'))∧   
      let A':=Finset.univ\N.biUnion markedWheelArcs
      let S':=SP\N.biUnion markedWheelSpokePairs
      let B:=markedFiniteResources (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2) πP Finset.univ SP
      let L:=markedFiniteResources (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2) πP A' S'
      let removed:=B.filter (markedInnerResource I J)\L;
      MarkedRemainderDivisible (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2) (HP true) A' S' (r+4)∧   
      (∀ a∈A',Sum.elim (fun e:EP=>e.val.1) (fun e:KP=>e.val.1) a∈I∧   Sum.elim (fun e:EP=>e.val.2) (fun e:KP=>e.val.2) a∈I)∧   
      (∀ z∈S',z.1∈I∧   z.2∈J)∧   L=B\N.biUnion markedWheelPhysicalResources∧   
      removed.filter (markedStarResource T Wrem)=E₀∧   removed.filter (markedInnerResource T Wrem)=∅∧   
      (∀ physical z,(((markedIncidentEdges (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2)
        πP (HP false) (HP true) physical z).filter (fun e=>markedActivePhysical (fun e:EP=>e.val.1) (fun e=>e.val.2)
        (fun e:KP=>e.val.1) (fun e=>e.val.2) πP (HP false) (HP true) e∈removed)).card:ℝ)≤  gammaLoss*I.card)∧   
      (∀ physical z,(((markedIncidentEdges (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2)
        πP (HP false) (HP true) physical z).filter (fun e=>markedActivePhysical (fun e:EP=>e.val.1) (fun e=>e.val.2)
        (fun e:KP=>e.val.1) (fun e=>e.val.2) πP (HP false) (HP true) e∈removed.filter (markedStarResource T Wrem))).card:ℝ)≤  sigmaLoss*I.card) :=by
  obtain ⟨c₀,hcover⟩:=marked_protected_cover_down_separated_tolerances_uniform_densities gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho₀ omega₀ t₀ p0 betaA aLoA BA hrho₀ hrho₀1 ho₀ ht₀ ht₀1 hp0 hp01 hbA haA hBA
  obtain ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hcover⟩:=hcover r hr hrc rho₀ omega₀ t₀ p0 betaA aLoA BA hrho₀ hrho₀1 ho₀ ht₀ ht₀1 hp0 hp01 hbA haA hBA
  refine ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩:=hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,?_⟩
  intro gammaLoss iota β aLo B hGammaLoss hIota hβ hBetaSmall haLo hB
  let ν:=gammaLoss*iota/32
  have hν:0<ν:=by dsimp [ν];positivity
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩:=hcover ν β aLo B hν hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,delta,hdelta,hcover⟩:=hcover p hp hp1 hpp
  refine ⟨θ,hθ,delta,hdelta,?_⟩
  intro x hx hxdelta sigmaLoss hSigmaLoss omegaI hIcut deltaI hoI hhI hdI hdIs
  let mu:=min x (min (gammaLoss/24) (sigmaLoss/12))
  have hmu:0< mu:=by dsimp [mu];positivity
  have hMuSmall:mu≤x:=min_le_left _ _
  have hmuGamma:mu≤gammaLoss/24:=(min_le_right _ _).trans (min_le_left _ _)
  have hmuSigma:mu≤sigmaLoss/12:=(min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨etaBal,hetaBal,NI,hcover⟩:=hcover x hx hxdelta mu hmu hMuSmall omegaI hIcut deltaI hoI hhI hdI hdIs
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨NN,hNN,hcover⟩:=hcover d hd
  refine ⟨NN,hNN,?_⟩
  intro rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt
  intro VP UP W V U Gamma Color _ _ _ _ _ _ _ _ _ _ _ _ hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    pRef kRef DRef hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    EP KP hDeepConfigs hDeepLoad I J xiDeep hXi0 hXiScale hDeepGap hTI hWremJ hI hIsize hJsize hNI hJlow hJI hTcut hWcut hTdeep hWdeep
    f ρ hf P pr kr sr D τweight hDlo hDhi weight hw Zinner hdtypesP hsepP Q S g c X
    hXimage hZimage hrows0 hconfigs0 hload0
    errR0 errI0 heR0 heI0 hErrR hErrI hZlow hrowEnd0 hidxEnd0
    errParent heP hNearP hMinP hTinner hErrParent pA DA hinnerSize hX hIotaSize hVhalf
    errInner errDeep heDeep hErrInner hErrDeep tailP headP ktailP kheadP SP EI KI tI hI' ktI khI H0Inner HKInner
    hbp hbm hbk hbw hc0 hcK hcs0 hcsK hDivP hBalI hBalT
  obtain ⟨E₀,N,hN,hDivN,hAN,hSN,hRem,hStar,hDeep,hInc,hStarInc⟩:=hcover rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt
    VP UP W V U Gamma Color hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    hDeepConfigs hDeepLoad I J xiDeep hXi0 hXiScale hDeepGap hTI hWremJ hI hIsize hJsize hNI hJlow hJI hTcut hWcut hTdeep hWdeep
    f ρ hf D τweight hDlo hDhi weight hw Zinner hdtypesP hsepP hXimage hZimage hrows0 hconfigs0 hload0
    errR0 errI0 heR0 heI0 hErrR hErrI hZlow hrowEnd0 hidxEnd0
    errParent heP hNearP hMinP hTinner hErrParent hinnerSize hX hVhalf
    errInner errDeep heDeep hErrInner hErrDeep hbp hbm hbk hbw hc0 hcK hcs0 hcsK hDivP hBalI hBalT
  have hAmbient:(Fintype.card (V⊕U):ℝ)≤ 2*Fintype.card VP:=by
    have hv:=Fintype.card_le_of_injective fA fA.injective
    have hu:=(Fintype.card_le_of_injective gA gA.injective).trans hUP
    rw [Fintype.card_sum,Nat.cast_add]
    exact_mod_cast (show Fintype.card V+Fintype.card U≤ 2*Fintype.card VP by omega)
  have hnuBound:ν≤ gammaLoss*iota/16:=by
    have hgi:=mul_nonneg hGammaLoss.le hIota.le
    dsimp [ν];linarith only [hgi]
  obtain ⟨hBudget,hStarBudget⟩:=marked_protected_final_incidence_budget
    gammaLoss sigmaLoss iota mu ν (3*mu*I.card) (Fintype.card VP) I.card (Fintype.card (V⊕U))
    hGammaLoss.le hIota.le hmu.le hν.le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hIotaSize hAmbient
    le_rfl (by linarith only [hmuGamma,hGammaLoss])
    (by linarith only [hmuSigma,hSigmaLoss]) hnuBound
  have hb:6*mu*I.card+4*(ν*Fintype.card (V⊕U))≤ gammaLoss*I.card:=by nlinarith only [hBudget]
  have hs:6*mu*I.card≤ sigmaLoss*I.card:=by nlinarith only [hStarBudget]
  refine ⟨E₀,N,hN,hDivN,hAN,hSN,hRem,hStar,hDeep,?_,?_⟩
  · intro physical z
    exact (hInc physical z).trans hb
  · intro physical z
    exact (hStarInc physical z).trans hs

end Oberwolfach
