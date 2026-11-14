module

public import Oberwolfach.MarkedProtectedCoverDownIterable
public import Oberwolfach.MarkedReferenceInputStability
public import Oberwolfach.MarkedGlobalCoverInputMargins
public import Oberwolfach.MarkedLocalCoverInputMargins
public import Oberwolfach.MarkedNestedIterationBalanceInputs
public import Oberwolfach.MarkedResourceDomainMonotonicity
public import Oberwolfach.MarkedIterationNeighbourhoodFromResources
public import Oberwolfach.MarkedIterationToleranceChoices

@[expose] public section

/-! Apply protected cover-down to the actual finite deletion of a fixed
reference. All analytic estimates of the current sample are derived from
those of the reference and the displayed global and star allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_protected_cover_down_from_fixed_reference (gamma pA0:ℝ)
    (hg:0< gamma) (hg1:gamma≤   1) (hpA0:0< pA0) (hpA01:pA0≤   1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤   r →            c₀≤   r+5 →            ∀ rho omega t p0 betaA aLoA BA:ℝ,
    0< rho →            rho≤   1 →            0< omega →            omega≤   1 →            0< t →            (r+4:ℝ)*t≤   1 →            
    pA0≤   rho*(r+4:ℝ)*t/2 →            0< p0 →            p0≤   rho*(r+4:ℝ)*t/2 →            p0≤   rho*t/2 →            p0≤   t →            0< betaA →            0< aLoA →            0< BA →            
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa →            kappa≤   kappa0 →            
    ∀ alphaInner omegaInner:ℝ,0< alphaInner →         0< omegaInner →         omegaInner≤   1 →         
    ∃ betaExt epsilonExt:ℝ,0< betaExt∧   0< epsilonExt∧   
    ∀ gammaLoss iota β aLo B:ℝ,0< gammaLoss →   0< iota →        0<β →        β≤   betaExt →        0< aLo →        0≤   B →        
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ) (hp:0< p) (hp1:p≤   1),p≤   pmax →            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x →    x≤   delta →    
    ∀ sigmaLoss:ℝ,0< sigmaLoss →  ∀ omegaI hIcut deltaI:ℝ,0< omegaI →    0< hIcut →    0< deltaI →    deltaI<1/4 →    
    ∃ etaBal:ℝ,0< etaBal∧   ∃ NI:ℕ,∀ d:ℕ,1≤   d →            ∃ N:ℕ,1≤   N∧   
    ∀ (VP UP W V U Gamma Color:Type) [Fintype VP] [Fintype UP] [LinearOrder VP] [DecidableEq UP]
      [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color],
    N≤   Fintype.card VP →            Fintype.card UP≤   Fintype.card VP →            omega*Fintype.card VP≤   (Fintype.card UP:ℝ) →            
    N≤   Fintype.card W →            omegaInner*Fintype.card (V⊕U)≤   (Fintype.card W:ℝ) →            
    ∀ (fA:V↪oVP) (gA:U↪UP) (PP:SimpleGraph VP) (πP:Equiv.Perm VP) (π:Equiv.Perm V),
    (∀ x,fA (π x)=πP (fA x)) →            
    ∀ (T:Finset VP) (Wrem:Finset UP),(∀ x,πP x∈T↔x∈T) →            
    Finset.univ.image fA=Finset.univ\T →            Finset.univ.image gA=Finset.univ\Wrem →            
    (T.card:ℝ)≤   kappa*Fintype.card VP →            (Wrem.card:ℝ)≤   kappa*Fintype.card VP →            
    (∀ x,(1/2+gamma/2)*Fintype.card VP≤   (PP.degree x:ℝ)) →            
    (∀ x,|(PP.degree x:ℝ)-2*Fintype.card UP/rho|≤   kappa*Fintype.card VP) →            
    ∀ (qP:UP →            Gamma →            ℝ) (sP:UP →            Color →            ℝ) (aP:Gamma) (cP:Color),
    (∀ u,qP u aP=t) →            (∀ u,sP u cP=(r+4:ℝ)*t) →            
    ∀ (σBase:RawMarkedOutcome VP UP Gamma Color) (HBase:Bool → VP → UP → Prop),
    let EBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) false
    let KBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) true
    let SBase:=Finset.univ.filter (fun z:VP×UP=>HBase false z.1 z.2∨HBase true z.1 z.2);
    ∀ (KA:Finset (EBase⊕KBase)) (KS:Finset (VP×UP)),KS⊆SBase → 
    let RBase:=markedFiniteResources (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP KA KS;
    (∀ physical z,(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
      (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈RBase)).card:ℝ)≤gammaLoss*Fintype.card VP) → 
    let σP:=rawMarkedDeleteRims σBase (markedSampleArcSetGraph PP πP d σBase KA).edgeFinset
    let HP:=markedDeletePhysicalSpokes HBase (markedFiniteSpokeGraph KS);
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card UP/rho;
    let CGlobal:=33*(r+5:ℝ)^4*(2*BA/p0^(2*(r+4)+1));
    kappa/4+gammaLoss≤kappa → kappa/4+4*gammaLoss≤kappa → 
    kappa/4+2*(r+12:ℝ)*gammaLoss≤kappa → kappa/4+(r+12:ℝ)*gammaLoss≤kappa → 
    gammaLoss≤(kappa-kappa/4)*omega → 
    2*gammaLoss≤(3/4)*(2*gamma)*pRef^2 → gammaLoss≤(2*gamma)*min pRef kRef/8 → 
    CGlobal*gammaLoss≤kappa/4 → CGlobal*gammaLoss≤thetaDeep/4 → 
    2*(r+5:ℝ)*gammaLoss≤min betaA (t/4) → (2*r+11:ℝ)*gammaLoss≤min betaA (t/4) → 
    MarkedReferenceStatistics PP πP d aP cP DRef (kappa/4) kappa (2*gamma) pRef kRef ((r+4:ℝ)*t) t σBase →            
    MarkedReferenceCutFamilies PP πP d aP cP (2*gamma) pRef kRef t σBase →            
    MarkedCommonConfigurationsWithSpokes r PP πP d betaA (kappa/4) σBase HBase →            
    MarkedRowsWithSpokes PP πP d (r+12) Finset.univ pRef kRef qP sP aP cP ((kappa/4)*Fintype.card VP) σBase HBase →            
    MarkedIndicesWithSpokes πP d (r+12) Finset.univ qP sP aP cP ((kappa/4)*Fintype.card VP) σBase HBase →            
    (∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes πP d σBase aP cP mark x u↔HBase mark x u) then (1:ℝ) else 0)≤   (kappa/4)*Fintype.card UP) →            
    (∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes πP d σBase aP cP mark x u↔HBase mark x u) then (1:ℝ) else 0)≤   (kappa/4)*Fintype.card VP) →            
    (Fintype.card VP:ℝ)/2≤   DRef →            DRef≤   2*Fintype.card VP →            
    ∀ (tauRef:ℝ) (weightRef:(Fin (r+4+1) →            VP) →            ℝ),SuccessorSequenceWeightConditions PP πP (3*d) DRef tauRef aLoA BA weightRef →            
    (let seed:=fun C:MarkedWheel (Prod.fst:VP×VP →            VP) Prod.snd Prod.fst Prod.snd (r+4) πP (3*d)
        (fun (_:VP) (_:UP)=>True) (fun _ _=>True)=>weightRef C.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
      ∀ root,rawMarkedWheelMarginal PP πP d pRef kRef qP sP aP cP root≠0 →            
        |typedMarkedPotentialLoad seed (rawMarkedPairRims PP πP d σBase) HBase root-1|≤   kappa/4) →            
    let EP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) false
    let KP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) true;
    MarkedLocalConfigurationsWithSpokes r PP πP d Finset.univ (3*(min betaA (t/4))) (3*(min betaA (t/4))) σBase HBase →    
    MarkedLocalSpokeLoadsWithSpokes PP πP d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weightRef (thetaDeep/4) σBase HBase →    
    ∀ (I:Finset VP) (J:Finset UP) (xiDeep:ℝ),0≤  xiDeep →   
    (4*Kgeom+3*r+50:ℝ)*xiDeep≤  kappa/2 →   (1+2/rho)*xiDeep≤  t*omegaInner/32 →   T⊆I →     Wrem⊆J →    
    (∀ v,πP v∈I↔v∈I) → 
    RBase.filter (markedInnerResource I J)=∅ → 
    (∀ physical z,(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
      (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈RBase.filter (markedStarResource I J))).card:ℝ)≤sigmaLoss*Fintype.card VP) → 
   
    (I.card:ℝ)≤   ξ*Fintype.card VP →    (J.card:ℝ)≤   ξ*Fintype.card VP →    
    NI≤   I.card →    omegaI*I.card≤   J.card →    J.card≤   I.card →    
    (T.card:ℝ)≤   hIcut*I.card →    (Wrem.card:ℝ)≤   hIcut*J.card →    
    (T.card:ℝ)≤   xiDeep*Fintype.card VP →    (Wrem.card:ℝ)≤   xiDeep*Fintype.card VP →    
    ∀ (f:W↪oV) (ρ:Equiv.Perm W),(∀ x,f (ρ x)=π (f x)) →            
    let P:=PP.comap fA;
    let pr:=pRef;let kr:=kRef;let sr:=(r+4:ℝ)*t;
    ∀ (D τweight:ℝ),
    (Fintype.card W:ℝ)/2≤   D →            D≤   2*Fintype.card W →            
    ∀ weight:(Fin (r+4+1) →            W) →            ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight →            
    ∀ Zinner:Finset U,
    (∀ u v,¬(HBase false v u∧   HBase true v u)) →       
    (∀ u v z,HBase false v u →       HBase true z u →       v≠πP z) →       
    let Q:=fun u=>qP (gA u)
    let S:=fun u=>sP (gA u)
    let g:=aP;let c:=cP
    let X:=Finset.univ.image f;
    X.image fA=I\T →      Zinner.image gA=J\Wrem →      
    let CLocal:=max 2 (max (2*(r+5:ℝ)) (max (2*r+11:ℝ) (15*(r+5:ℝ)^4*(2*B/p0^(2*(r+4)+1)))));
    iota*Fintype.card VP/4≤(Fintype.card W:ℝ) → 
    4*CLocal*sigmaLoss/iota≤min (t/8) (min β (η/4)) → 
    2*(r+12:ℝ)*sigmaLoss≤x/2 → (r+6:ℝ)*sigmaLoss≤x/4 → 
    MarkedRowsWithSpokes (PP.comap (f.comp fA)) ρ d 1 Finset.univ pr kr Q S g c ((t/8)*Fintype.card W)
      (rawMarkedRestrictPair (f.comp fA) gA σBase) (fun b x u=>HBase b (fA (f x)) (gA u)) →       
    MarkedLocalConfigurationsWithSpokes r (PP.comap (f.comp fA)) ρ d Finset.univ (3*β) (3*β)
      (rawMarkedRestrictPair (f.comp fA) gA σBase) (fun b x u=>HBase b (fA (f x)) (gA u)) →       
    MarkedLocalSpokeLoadsWithSpokes (PP.comap (f.comp fA)) ρ d (r+4) D pr kr sr weight (η/4)
      (rawMarkedRestrictPair (f.comp fA) gA σBase) (fun b x u=>HBase b (fA (f x)) (gA u)) →       
    ∀ errR0 errI0:ℝ,0≤   errR0 →       0≤   errI0 →       

    errR0≤   (x/2)*Fintype.card VP →     errI0≤   (x/2)*Fintype.card VP →     
    omegaInner*Fintype.card (V⊕U)≤   (Zinner.card:ℝ) →         

    MarkedRowsWithSpokes PP πP d (r+12) (X.image fA) pr kr qP sP g c errR0 σBase HBase →       
    MarkedIndicesWithSpokes πP d (r+12) (Zinner.image gA) qP sP g c errI0 σBase HBase →       

    ∀ errParent:ℝ,0≤   errParent →      
    (∀ v,|((PP.neighborFinset v∩I).card:ℝ)-2*J.card/rho|≤   errParent) →      
    (∀ v,(1/2+2*alphaInner)*I.card≤   ((PP.neighborFinset v∩I).card:ℝ)) →      
    (T.card:ℝ)≤   alphaInner*I.card →      
    errParent≤   x*Fintype.card VP →     
    let pA:=rho*(r+4:ℝ)*t/2
    let DA:=2*Fintype.card U/rho;
    ( (ordinaryInnerVertices X Zinner).card:ℝ)≤   ξ*Fintype.card V  →            
    (∀ x,π x∈X↔x∈X)  →            
    iota*Fintype.card VP≤  I.card →  
    (Fintype.card VP:ℝ)/2≤  Fintype.card V →    
    ∀ errInner errDeep:ℝ,0≤   errDeep →    errInner≤   (x/2)*Fintype.card VP →    errDeep≤   (x/2)*Fintype.card VP →    
    let tailP:=fun e:EP=>e.val.1
    let headP:=fun e:EP=>e.val.2
    let ktailP:=fun e:KP=>e.val.1
    let kheadP:=fun e:KP=>e.val.2
    let SP:=Finset.univ.filter (fun z:VP×UP=>HP false z.1 z.2∨HP true z.1 z.2)
    (∀ z,Sum.elim (fun v=>v∈I) (fun u=>u∈J) z → ∀ i,
      |markedFiniteDomainBalance (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) Finset.univ SBase (r+4) I J z i|≤etaBal*I.card) → 
    (∀ mark,BipartiteLargeCut (fun x:I=>fun y:I=>markedPhysicalRim PP πP (3*d)
      (fun e=>σBase (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) → 
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:I=>fun u:J=>HBase mark x.val u.val)) deltaI (2*hIcut)) → 
    MarkedRemainderDivisible tailP headP ktailP kheadP (HP true) Finset.univ SP (r+4) →    
    (∀ z i,|markedFiniteDomainBalance (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) Finset.univ SBase (r+4) I J z i|≤   errInner) →    
    (∀ z i,|markedFiniteDomainBalance (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) Finset.univ SBase (r+4) T Wrem z i|≤   errDeep) →    
    ∃ E₀:Finset (Finset VP⊕(VP×UP)),
    ∃ N:Finset (MarkedWheel (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2)
      (r+4) πP (3*d) (HP false) (HP true)),
      (∀ Y∈N,∀ Y'∈N,Y≠Y' →    Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Y'))∧   
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
        (fun e:KP=>e.val.1) (fun e=>e.val.2) πP (HP false) (HP true) e∈removed.filter (markedStarResource T Wrem))).card:ℝ)≤  sigmaLoss*I.card) := by
  obtain ⟨c₀,hcover⟩ := marked_protected_cover_down_iterable gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  obtain ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hcover⟩ :=
    hcover r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  refine ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩ := hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,?_⟩
  intro gammaLoss iota β aLo B hGammaLoss hIota hβ hBetaSmall haLo hB
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩ :=
    hcover gammaLoss iota β aLo B hGammaLoss hIota hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,delta,hdelta,hcover⟩ := hcover p hp hp1 hpp
  refine ⟨θ,hθ,delta,hdelta,?_⟩
  intro x hx hxdelta sigmaLoss hSigmaLoss omegaI hIcut deltaI hoI hhI hdI hdIs
  obtain ⟨etaBal,hetaBal,NI,hcover⟩ := hcover x hx hxdelta sigmaLoss hSigmaLoss omegaI hIcut deltaI hoI hhI hdI hdIs
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨NN,hNN,hcover⟩ := hcover d hd
  refine ⟨NN,hNN,?_⟩
  intro VP UP W V U Gamma Color _ _ _ _ _ _ _ _ _ _ _ _ hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP
    σBase HBase EBase KBase SBase KA KS hKS RBase hGlobal σP HP pRef kRef DRef CGlobal
    hG1 hG2 hG3 hG4 hGSp hGStat hGCut hGL hGLL hGC hGP
    hstats0 hcuts0 hconfigsP0 hrowsP0 hindicesP0 hrowOld0 hcolOld0 hDloP hDhiP tauRef weightRef hwRef hloadRef0
    EP KP hDeepConfigs0 hDeepLoad0 I J xiDeep hXi0 hXiScale hDeepGap hTI hWremJ hI hEmptyBase hStarBase
    hIsize hJsize hNI hJlow hJI hTcut hWcut hTdeep hWdeep
    f ρ hf P pr kr sr D τweight hDlo hDhi weight hw Zinner hdtypesBase hsepBase Q S g c X
    hXimage hZimage CLocal hLocalSize hLocalBudget hRowScale hBalanceScale hrows00 hconfigs00 hload00
    errR0 errI0 heR0 heI0 hErrR0 hErrI0 hZlow hrowEnd00 hidxEnd00
    errParent heP hNearP hMinP hTinner hErrParent pA DA hinnerSize hX hIotaSize hVhalf
    errInner errDeep heDeep hErrInner0 hErrDeep0 tailP headP ktailP kheadP SP
    hInnerBase hCutRBase hCutSBase hDivP hBalIBase hBalTBase
  have hnP0 : 0<Fintype.card VP := lt_of_lt_of_le (by omega) hnP
  have hnW0 : 0<Fintype.card W := lt_of_lt_of_le (by omega) hnW
  have hnPReal : (0:ℝ)≤Fintype.card VP := Nat.cast_nonneg _
  have hRBase : ∀ a∈KA,Sum.inl (markedPhysicalEdge (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP a)∈RBase := by
    intro a ha;exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have hKSBase : ∀ z∈KS,HBase false z.1 z.2∨HBase true z.1 z.2 :=
    fun z hz=>(Finset.mem_filter.mp (hKS hz)).2
  have hSBase : ∀ z∈KS,Sum.inr z∈RBase := by
    intro z hz;exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
  let DR := markedSampleArcSetGraph PP πP d σBase KA
  let DS := markedFiniteSpokeGraph KS
  obtain ⟨hDR,hDS⟩ := marked_finite_global_deletion_graph_bounds
    (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2)
    πP HBase KA KS RBase (gammaLoss*Fintype.card VP) hRBase hKSBase hSBase hGlobal
  have hkRef : kRef=rho*t/2 := by
    dsimp [kRef,pRef]
    have hne : (r:ℝ)+4≠0 := by positivity
    field_simp
  have hs1 : (r+4:ℝ)*t≤1 := ht1
  have ht0 : t≤(r+4:ℝ)*t := by nlinarith only [ht,show (0:ℝ)≤r by positivity]
  have hpRef1 : pRef≤1 := by
    have h := mul_le_mul_of_nonneg_right hrho1 (show 0≤(r+4:ℝ)*t by positivity)
    dsimp [pRef];nlinarith only [h,ht1]
  have hkRef1 : kRef≤1 := by rw [hkRef];nlinarith only [mul_le_mul_of_nonneg_right hrho1 ht.le,ht0,ht1]
  have hp0k : p0≤kRef := by rwa [hkRef]
  have hp0s : p0≤(r+4:ℝ)*t := hpt.trans ht0
  obtain ⟨hstats,hcuts,hconfigsP,hrowsP,hindicesP,hrowOld,hcolOld⟩ :=
    marked_reference_input_stability r (r+12) PP πP d aP cP DRef pRef kRef ((r+4:ℝ)*t) t betaA
      (kappa/4) kappa (2*gamma) gammaLoss omega hGammaLoss.le (by positivity) hnP0 hUPlow
      hG1 hG2 (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG3) (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG4) hGSp (by linarith only [hkappa]) hGStat hGCut
      qP sP σBase HBase hstats0 hcuts0 hconfigsP0 hrowsP0 hindicesP0 hrowOld0 hcolOld0 DR DS hDR hDS
  have hgam : (2*gamma)/2=gamma := by ring
  rw [hgam] at hstats hcuts
  obtain ⟨hloadRef,hDeepLoad,hDeepConfigs⟩ := marked_global_cover_input_margins
    (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2)
    πP HBase KA KS RBase gammaLoss hGammaLoss.le hRBase hKSBase hSBase hGlobal PP r d hnP0 hUP
    DRef tauRef aLoA BA hDloP hDhiP pRef kRef ((r+4:ℝ)*t) p0 hp0 hpr hp0k hp0s
    hpRef1 hkRef1 hs1 hBA.le weightRef hwRef (kappa/4) kappa thetaDeep (min betaA (t/4))
    hkappa.le hΘDeep.le le_rfl hGL hGLL hGC hGP σBase
    (fun root=>rawMarkedWheelMarginal PP πP d pRef kRef qP sP aP cP root≠0)
    hloadRef0 hDeepLoad0 hDeepConfigs0
  have hLocalImage : ∀ w:W,(f.comp fA) w∈I := by
    intro w
    have hwX : f w∈X := Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩
    have hh : fA (f w)∈I\T := hXimage ▸ Finset.mem_image.mpr ⟨f w,hwX,rfl⟩
    exact (Finset.mem_sdiff.mp hh).1
  have hCL0 : 0≤CLocal := le_trans (by norm_num) (le_max_left _ _)
  have hCL2 : 2≤CLocal := le_max_left _ _
  have hCLC : 2*(r+5:ℝ)≤CLocal := (le_max_left _ _).trans (le_max_right _ _)
  have hCLP : (2*r+11:ℝ)≤CLocal := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCLL : 15*(r+5:ℝ)^4*(2*B/p0^(2*(r+4)+1))≤CLocal :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hw' : SuccessorSequenceWeightConditions (PP.comap (f.comp fA)) ρ (3*d) D τweight aLo B weight := hw
  obtain ⟨hrows0,hconfigs0,hload0⟩ := marked_local_cover_input_margins
    (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2)
    πP HBase KA KS RBase I J hI sigmaLoss iota CLocal t β η hSigmaLoss.le hIota hCL0
    hRBase hKSBase hSBase hStarBase (f.comp fA) gA hLocalImage PP ρ d r hnW0 hLocalSize
    D τweight aLo B hDlo hDhi pRef kRef ((r+4:ℝ)*t) p0 hp0 hpr hp0k hp0s
    hpRef1 hkRef1 hs1 hB Q S g c weight hw' hCL2 hCLC hCLP hCLL hLocalBudget
    σBase hrows00 hconfigs00 hload00
  have hdtypesP : ∀ u v,¬(HP false v u∧HP true v u) :=
    fun u v hh=>hdtypesBase u v ⟨hh.1.1,hh.2.1⟩
  have hsepP : ∀ u v z,HP false v u→HP true z u→v≠πP z :=
    fun u v z hv hz=>hsepBase u v z hv.1 hz.1
  have hXsub : X.image fA⊆I := by rw [hXimage];exact Finset.sdiff_subset
  have hZsub : Zinner.image gA⊆J := by rw [hZimage];exact Finset.sdiff_subset
  have hXinv : ∀ v,πP v∈X.image fA↔v∈X.image fA := by
    intro v;rw [hXimage];simp only [Finset.mem_sdiff,hI,hT]
  have hStarSmall : ∀ physical z,(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
      (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈RBase.filter
          (markedStarResource (X.image fA) (Zinner.image gA)))).card:ℝ)≤sigmaLoss*Fintype.card VP := by
    intro physical z
    apply le_trans (b:=(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
      (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈RBase.filter
          (markedStarResource I J))).card:ℝ))
    · apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro a ha
      obtain ⟨hi,ha⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha,hin⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hi,Finset.mem_filter.mpr ⟨ha,markedStarResource_mono hXsub hZsub _ hin⟩⟩
    · exact hStarBase physical z
  obtain ⟨_,_,hrowEnd0,hidxEnd0⟩ := marked_iteration_neighbourhoods_from_resource_bounds
    (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2)
    πP HBase KA KS RBase (X.image fA) (Zinner.image gA) hXinv
    (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) (by positivity) (by positivity)
    hRBase hKSBase hSBase hGlobal hStarSmall PP d (r+12) pRef kRef qP sP aP cP
    ((kappa/4)*Fintype.card VP) ((kappa/4)*Fintype.card VP) errR0 errI0 σBase
    hrowsP0 hindicesP0 hrowEnd00 hidxEnd00
  let errRnew := errR0+2*(r+12:ℝ)*(sigmaLoss*Fintype.card VP)
  let errInew := errI0+(r+12:ℝ)*(sigmaLoss*Fintype.card VP)
  have heRnew : 0≤errRnew := by dsimp [errRnew];positivity
  have heInew : 0≤errInew := by dsimp [errInew];positivity
  have hErrRnew : errRnew≤x*Fintype.card VP := by
    dsimp [errRnew]
    nlinarith only [hErrR0,mul_le_mul_of_nonneg_right hRowScale (Nat.cast_nonneg (α:=ℝ) (Fintype.card VP))]
  have hErrInew : errInew≤x*Fintype.card VP := by
    dsimp [errInew]
    nlinarith only [hErrI0,mul_le_mul_of_nonneg_right hRowScale (Nat.cast_nonneg (α:=ℝ) (Fintype.card VP)),
      show 0≤(r+12:ℝ)*(sigmaLoss*Fintype.card VP) by positivity]
  have hBalanceScale' : (↑(r+4)+2:ℝ)*sigmaLoss≤x/4 := by
    convert hBalanceScale using 1 <;> push_cast <;> ring
  obtain ⟨hBalI,hBalT⟩ := marked_nested_iteration_balance_inputs PP πP d (r+4) σBase HBase I T J Wrem
    hI hT hTI hWremJ errInner errDeep x sigmaLoss hSigmaLoss.le hx.le hErrInner0 hErrDeep0 hBalanceScale'
    KA KS hKS hEmptyBase hStarBase hBalIBase hBalTBase
  obtain ⟨hbp,hbm,hbk,hbw,hc0,hcK,hcs0,hcsK⟩ := marked_actual_inner_correction_inputs
    PP πP d (r+4) σBase HBase (fun v u=>hdtypesBase u v) I J hI (etaBal*I.card) deltaI (2*hIcut)
    hCutRBase hCutSBase KA KS hKS hEmptyBase hInnerBase
  exact hcover VP UP W V U Gamma Color hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    hDeepConfigs hDeepLoad I J xiDeep hXi0 hXiScale hDeepGap hTI hWremJ hI hIsize hJsize hNI hJlow hJI hTcut hWcut hTdeep hWdeep
    f ρ hf D τweight hDlo hDhi weight hw Zinner hdtypesP hsepP hXimage hZimage hrows0 hconfigs0 hload0
    errRnew errInew heRnew heInew hErrRnew hErrInew hZlow (by simpa only [errRnew,X,pRef,kRef,σP,HP,markedSampleArcSetGraph,Nat.cast_add,Nat.cast_ofNat] using hrowEnd0) (by simpa only [errInew,σP,HP,markedSampleArcSetGraph,Nat.cast_add,Nat.cast_ofNat] using hidxEnd0)
    errParent heP hNearP hMinP hTinner hErrParent hinnerSize hX hIotaSize hVhalf
    (x*Fintype.card VP) (x*Fintype.card VP) (by positivity) le_rfl le_rfl
    hbp hbm hbk hbw hc0 hcK hcs0 hcsK hDivP hBalI hBalT

end Oberwolfach
