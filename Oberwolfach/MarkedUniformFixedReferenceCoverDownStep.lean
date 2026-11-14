module

public import Oberwolfach.MarkedFixedReferenceCoverDownStep
public import Oberwolfach.MarkedDeletedCoverFixedRemainder
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

theorem marked_uniform_fixed_reference_cover_down_step (gamma pA0:ℝ)
    (hg:0< gamma) (hg1:gamma≤   1) (hpA0:0< pA0) (hpA01:pA0≤   1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤   r →            c₀≤   r+5 →            ∀ rho omega t p0 betaA aLoA BA:ℝ,
    0< rho →            rho≤   1 →            0< omega →            omega≤   1 →            0< t →            (r+4:ℝ)*t≤   1 →            
    pA0≤   rho*(r+4:ℝ)*t/2 →            0< p0 →            p0≤   rho*(r+4:ℝ)*t/2 →            p0≤   rho*t/2 →            p0≤   t →            0< betaA →            0< aLoA →            0< BA →            
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa →            kappa≤   kappa0 →            
    ∀ alphaInner omegaInner:ℝ,0< alphaInner →         0< omegaInner →         omegaInner≤   1 →         
    ∃ betaExt epsilonExt:ℝ,0< betaExt∧   0< epsilonExt∧   
    ∃ gammaMax:ℝ,0<gammaMax ∧ ∀ gammaLoss iota β aLo B:ℝ,0<gammaLoss → gammaLoss≤gammaMax →   0< iota →        0<β →        β≤   betaExt →        0< aLo →        0≤   B →        
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ) (hp:0< p) (hp1:p≤   1),p≤   pmax →            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x →    x≤   delta →    
    ∃ sigmaMax:ℝ,0<sigmaMax ∧ ∀ sigmaLoss:ℝ,0<sigmaLoss → sigmaLoss≤sigmaMax →  ∀ omegaI hIcut deltaI:ℝ,0< omegaI →    0< hIcut →    0< deltaI →    deltaI<1/4 →    
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
    ∃ N:Finset (MarkedWheel (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) (r+4) πP (3*d) (HBase false) (HBase true)),
      (∀ Y∈N,∀ Z∈N,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) ∧
      N.biUnion markedWheelArcs⊆Finset.univ\KA ∧ N.biUnion markedWheelSpokePairs⊆SBase\KS ∧
      let AR:=Finset.univ\(KA∪N.biUnion markedWheelArcs)
      let SR:=SBase\(KS∪N.biUnion markedWheelSpokePairs)
      let BBase:=markedFiniteResources (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP Finset.univ SBase
      let L:=markedFiniteResources (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP AR SR;
      MarkedRemainderDivisible (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) AR SR (r+4) ∧
      (∀ a∈AR,Sum.elim (fun e:EBase=>e.val.1) (fun e:KBase=>e.val.1) a∈I ∧
        Sum.elim (fun e:EBase=>e.val.2) (fun e:KBase=>e.val.2) a∈I) ∧
      (∀ z∈SR,z.1∈I∧z.2∈J) ∧
      ∃ F⊆BBase.filter (markedInnerResource I J),
        L=BBase.filter (markedInnerResource I J)\F ∧
        F.filter (markedInnerResource T Wrem)=∅ ∧
        (∀ physical z,(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
          (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
          (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
            (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈F)).card:ℝ)≤gammaLoss*I.card) ∧
        (∀ physical z,(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
          (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
          (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
            (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈F.filter (markedStarResource T Wrem))).card:ℝ)≤sigmaLoss*I.card) := by
  obtain ⟨c₀,hcover⟩ := marked_fixed_reference_cover_down_step gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  obtain ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hcover⟩ :=
    hcover r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  refine ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩ := hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  let pRef0:=rho*(r+4:ℝ)*t/2
  let kRef0:=pRef0/(r+4:ℝ)
  let CGlobal0:=33*(r+5:ℝ)^4*(2*BA/p0^(2*(r+4)+1))
  obtain ⟨gammaMax,hGammaMax,hGlobalChoice⟩ := marked_iteration_global_tolerance_choice
    r (r+12) kappa (2*gamma) pRef0 kRef0 omega CGlobal0 thetaDeep (min betaA (t/4))
    hkappa (by positivity) (by dsimp [pRef0];positivity) (by dsimp [kRef0,pRef0];positivity)
    ho (by dsimp [CGlobal0];positivity) hΘDeep (by positivity)
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,gammaMax,hGammaMax,?_⟩
  intro gammaLoss iota β aLo B hGammaLoss hGammaBound hIota hβ hBetaSmall haLo hB
  obtain ⟨hG1,hG2,hG3,hG4,hGSp,_,hGStat,hGCut,hGL,hGLL,hGC,hGP⟩ :=
    hGlobalChoice (kappa/4) gammaLoss le_rfl hGammaLoss.le hGammaBound
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩ :=
    hcover gammaLoss iota β aLo B hGammaLoss hIota hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,delta,hdelta,hcover⟩ := hcover p hp hp1 hpp
  refine ⟨θ,hθ,delta,hdelta,?_⟩
  intro x hx hxdelta
  let CLocal0:=max 2 (max (2*(r+5:ℝ)) (max (2*r+11:ℝ) (15*(r+5:ℝ)^4*(2*B/p0^(2*(r+4)+1)))))
  obtain ⟨sigmaMax,hSigmaMax,hLocalChoice⟩ := marked_iteration_local_tolerance_choice
    (r+4) (r+12) x iota CLocal0 t β η hx hIota
    (le_trans (by norm_num) (le_max_left _ _)) ht hβ hη
  refine ⟨sigmaMax,hSigmaMax,?_⟩
  intro sigmaLoss hSigmaLoss hSigmaBound omegaI hIcut deltaI hoI hhI hdI hdIs
  obtain ⟨hBalanceScale,hRowScale,hLocalBudget⟩ := hLocalChoice sigmaLoss hSigmaLoss.le hSigmaBound
  obtain ⟨etaBal,hetaBal,NI,hcover⟩ := hcover x hx hxdelta sigmaLoss hSigmaLoss omegaI hIcut deltaI hoI hhI hdI hdIs
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨NN,hNN,hcover⟩ := hcover d hd
  refine ⟨NN,hNN,?_⟩
  intro VP UP W V U Gamma Color _ _ _ _ _ _ _ _ _ _ _ _ hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP
    σBase HBase EBase KBase SBase KA KS hKS RBase hGlobal σP HP pRef kRef DRef CGlobal
    hstats0 hcuts0 hconfigsP0 hrowsP0 hindicesP0 hrowOld0 hcolOld0 hDloP hDhiP tauRef weightRef hwRef hloadRef0
    EP KP hDeepConfigs0 hDeepLoad0 I J xiDeep hXi0 hXiScale hDeepGap hTI hWremJ hI hEmptyBase hStarBase
    hIsize hJsize hNI hJlow hJI hTcut hWcut hTdeep hWdeep
    f ρ hf P pr kr sr D τweight hDlo hDhi weight hw Zinner hdtypesBase hsepBase Q S g c X
    hXimage hZimage CLocal hLocalSize hrows00 hconfigs00 hload00
    errR0 errI0 heR0 heI0 hErrR0 hErrI0 hZlow hrowEnd00 hidxEnd00
    errParent heP hNearP hMinP hTinner hErrParent pA DA hinnerSize hX hIotaSize hVhalf
    errInner errDeep heDeep hErrInner0 hErrDeep0 tailP headP ktailP kheadP SP
    hInnerBase hCutRBase hCutSBase hDivP hBalIBase hBalTBase
  exact hcover VP UP W V U Gamma Color hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP
    σBase HBase KA KS hKS hGlobal
    hG1 hG2 (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG3)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hG4) hGSp hGStat hGCut hGL hGLL hGC hGP
    hstats0 hcuts0 hconfigsP0 hrowsP0 hindicesP0 hrowOld0 hcolOld0 hDloP hDhiP tauRef weightRef hwRef hloadRef0
    hDeepConfigs0 hDeepLoad0 I J xiDeep hXi0 hXiScale hDeepGap hTI hWremJ hI hEmptyBase hStarBase
    hIsize hJsize hNI hJlow hJI hTcut hWcut hTdeep hWdeep
    f ρ hf D τweight hDlo hDhi weight hw Zinner hdtypesBase hsepBase
    hXimage hZimage hLocalSize hLocalBudget
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hRowScale)
    (by convert hBalanceScale using 1 <;> push_cast <;> ring)
    hrows00 hconfigs00 hload00
    errR0 errI0 heR0 heI0 hErrR0 hErrI0 hZlow hrowEnd00 hidxEnd00
    errParent heP hNearP hMinP hTinner hErrParent hinnerSize hX hIotaSize hVhalf
    errInner errDeep heDeep hErrInner0 hErrDeep0 hInnerBase hCutRBase hCutSBase hDivP hBalIBase hBalTBase

end Oberwolfach
