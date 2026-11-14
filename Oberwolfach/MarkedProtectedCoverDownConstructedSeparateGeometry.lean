module

public import Oberwolfach.MarkedProtectedCoverDownSeparateGeometryFromPackings
public import Oberwolfach.MarkedConstructedDeepCanonicalEstimates
public import Oberwolfach.MarkedFiniteCorrectionIncidence
public import Oberwolfach.MarkedFiniteInnerGraphSupport

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

theorem marked_protected_cover_down_constructed_separate_geometry (gamma pA0:ℝ)
    (hg:0<gamma) (hg1:gamma≤  1) (hpA0:0<pA0) (hpA01:pA0≤  1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤  r→          c₀≤  r+5→          ∀ rho omega t p0 betaA aLoA BA:ℝ,
    0<rho→          rho≤  1→          0<omega→          omega≤  1→          0<t→          (r+4:ℝ)*t≤  1→          
    pA0≤  rho*(r+4:ℝ)*t/2→          0<p0→          p0≤  rho*(r+4:ℝ)*t/2→          p0≤  rho*t/2→          p0≤  t→          0<betaA→          0<aLoA→          0<BA→          
    ∃ Kgeom:ℕ,0<Kgeom∧  ∃ kappa0 ξ thetaDeep:ℝ,0<kappa0∧  0<ξ∧  0<thetaDeep∧  ∀ kappa:ℝ,0<kappa→          kappa≤  kappa0→          
    ∀ alphaInner omegaInner:ℝ,0<alphaInner→       0<omegaInner→       omegaInner≤  1→       
    ∃ betaExt epsilonExt:ℝ,0<betaExt∧  0<epsilonExt∧  
    ∀ ν β aLo B:ℝ,0<ν→      0<β→      β≤  betaExt→      0<aLo→      0≤  B→      
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧  0<ηEnd∧  0<ζ∧  0<ζD∧  0<pmax∧  pmax≤  1/8∧  
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤  1),p≤  pmax→          ∃ θ:ℝ,0<θ∧  
    ∃ delta:ℝ,0<delta∧  ∀ x:ℝ,0<x→  x≤  delta→  
    ∀ omegaI hIcut deltaI:ℝ,0<omegaI→  0<hIcut→  0<deltaI→  deltaI<1/4→  
    ∃ etaBal:ℝ,0<etaBal∧  ∃ NI:ℕ,∀ d:ℕ,1≤  d→          ∃ N:ℕ,1≤  N∧  
    ∀ (VP UP W V U Gamma Color:Type) [Fintype VP] [Fintype UP] [LinearOrder VP] [DecidableEq UP]
      [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color],
    N≤  Fintype.card VP→          Fintype.card UP≤  Fintype.card VP→          omega*Fintype.card VP≤  (Fintype.card UP:ℝ)→          
    N≤  Fintype.card W→          omegaInner*Fintype.card (V⊕U)≤  (Fintype.card W:ℝ)→          
    ∀ (fA:V↪oVP) (gA:U↪UP) (PP:SimpleGraph VP) (πP:Equiv.Perm VP) (π:Equiv.Perm V),
    (∀ x,fA (π x)=πP (fA x))→          
    ∀ (T:Finset VP) (Wrem:Finset UP),(∀ x,πP x∈T↔x∈T)→          
    Finset.univ.image fA=Finset.univ\T→          Finset.univ.image gA=Finset.univ\Wrem→          
    (T.card:ℝ)≤  kappa*Fintype.card VP→          (Wrem.card:ℝ)≤  kappa*Fintype.card VP→          
    (∀ x,(1/2+gamma/2)*Fintype.card VP≤  (PP.degree x:ℝ))→          
    (∀ x,|(PP.degree x:ℝ)-2*Fintype.card UP/rho|≤  kappa*Fintype.card VP)→          
    ∀ (qP:UP→          Gamma→          ℝ) (sP:UP→          Color→          ℝ) (aP:Gamma) (cP:Color),
    (∀ u,qP u aP=t)→          (∀ u,sP u cP=(r+4:ℝ)*t)→          
    ∀ (σP:RawMarkedOutcome VP UP Gamma Color) (HP:Bool→          VP→          UP→          Prop),
    let pRef:=rho*(r+4:ℝ)*t/2
    let kRef:=pRef/(r+4:ℝ)
    let DRef:=2*Fintype.card UP/rho;
    MarkedReferenceStatistics PP πP d aP cP DRef kappa kappa gamma pRef kRef ((r+4:ℝ)*t) t σP→          
    MarkedReferenceCutFamilies PP πP d aP cP gamma pRef kRef t σP→          
    MarkedCommonConfigurationsWithSpokes r PP πP d betaA kappa σP HP→          
    MarkedRowsWithSpokes PP πP d (r+12) Finset.univ pRef kRef qP sP aP cP (kappa*Fintype.card VP) σP HP→          
    MarkedIndicesWithSpokes πP d (r+12) Finset.univ qP sP aP cP (kappa*Fintype.card VP) σP HP→          
    (∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤  kappa*Fintype.card UP)→          
    (∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes πP d σP aP cP mark x u↔HP mark x u) then (1:ℝ) else 0)≤  kappa*Fintype.card VP)→          
    (Fintype.card VP:ℝ)/2≤  DRef→          DRef≤  2*Fintype.card VP→          
    ∀ (tauRef:ℝ) (weightRef:(Fin (r+4+1)→          VP)→          ℝ),SuccessorSequenceWeightConditions PP πP (3*d) DRef tauRef aLoA BA weightRef→          
    (let seed:=fun C:MarkedWheel (Prod.fst:VP×VP→          VP) Prod.snd Prod.fst Prod.snd (r+4) πP (3*d)
        (fun (_:VP) (_:UP)=>True) (fun _ _=>True)=>weightRef C.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4));
      ∀ root,rawMarkedWheelMarginal PP πP d pRef kRef qP sP aP cP root≠0→          
        |typedMarkedPotentialLoad seed (rawMarkedPairRims PP πP d σP) HP root-1|≤  kappa)→          
    let EP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) false
    let KP:=MarkedSampleArc PP πP (3*d) (fun e=>σP (Sum.inl e)) true;
    MarkedLocalConfigurationsWithSpokes r PP πP d Finset.univ (2*(min betaA (t/4))) (2*(min betaA (t/4))) σP HP→  
    MarkedLocalSpokeLoadsWithSpokes PP πP d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weightRef (thetaDeep/2) σP HP→  
    ∀ (I:Finset VP) (J:Finset UP) (xiDeep:ℝ),0≤ xiDeep→ 
    (4*Kgeom+3*r+50:ℝ)*xiDeep≤ kappa/2→ (1+2/rho)*xiDeep≤ t*omegaInner/32→ T⊆I→   Wrem⊆J→  
    (∀ v,πP v∈I↔v∈I)→  
    (I.card:ℝ)≤  ξ*Fintype.card VP→  (J.card:ℝ)≤  ξ*Fintype.card VP→  
    NI≤  I.card→  omegaI*I.card≤  J.card→  J.card≤  I.card→  
    (T.card:ℝ)≤  hIcut*I.card→  (Wrem.card:ℝ)≤  hIcut*J.card→  
    (T.card:ℝ)≤  xiDeep*Fintype.card VP→  (Wrem.card:ℝ)≤  xiDeep*Fintype.card VP→  
    ∀ (f:W↪oV) (ρ:Equiv.Perm W),(∀ x,f (ρ x)=π (f x))→          
    let P:=PP.comap fA;
    let pr:=pRef;let kr:=kRef;let sr:=(r+4:ℝ)*t;
    ∀ (D τweight:ℝ),
    (Fintype.card W:ℝ)/2≤  D→          D≤  2*Fintype.card W→          
    ∀ weight:(Fin (r+4+1)→          W)→          ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight→          
    ∀ Zinner:Finset U,
    (∀ u v,¬(HP false v u∧  HP true v u))→     
    (∀ u v z,HP false v u→     HP true z u→     v≠πP z)→     
    let Q:=fun u=>qP (gA u)
    let S:=fun u=>sP (gA u)
    let g:=aP;let c:=cP
    let X:=Finset.univ.image f;
    X.image fA=I\T→    Zinner.image gA=J\Wrem→    
    MarkedRowsWithSpokes (PP.comap (f.comp fA)) ρ d 1 Finset.univ pr kr Q S g c ((t/4)*Fintype.card W)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→     
    MarkedLocalConfigurationsWithSpokes r (PP.comap (f.comp fA)) ρ d Finset.univ (2*β) (2*β)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→     
    MarkedLocalSpokeLoadsWithSpokes (PP.comap (f.comp fA)) ρ d (r+4) D pr kr sr weight (η/2)
      (rawMarkedRestrictPair (f.comp fA) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))→     
    ∀ errR0 errI0:ℝ,0≤  errR0→     0≤  errI0→     

    errR0≤  x*Fintype.card VP→   errI0≤  x*Fintype.card VP→   
    omegaInner*Fintype.card (V⊕U)≤  (Zinner.card:ℝ)→       

    MarkedRowsWithSpokes PP πP d (r+12) (X.image fA) pr kr qP sP g c errR0 σP HP→     
    MarkedIndicesWithSpokes πP d (r+12) (Zinner.image gA) qP sP g c errI0 σP HP→     

    ∀ errParent:ℝ,0≤  errParent→    
    (∀ v,|((PP.neighborFinset v∩I).card:ℝ)-2*J.card/rho|≤  errParent)→    
    (∀ v,(1/2+2*alphaInner)*I.card≤  ((PP.neighborFinset v∩I).card:ℝ))→    
    (T.card:ℝ)≤  alphaInner*I.card→    
    errParent≤  x*Fintype.card VP→   
    let pA:=rho*(r+4:ℝ)*t/2
    let DA:=2*Fintype.card U/rho;
    ( (ordinaryInnerVertices X Zinner).card:ℝ)≤  ξ*Fintype.card V →          
    (∀ x,π x∈X↔x∈X) →          
    (Fintype.card VP:ℝ)/2≤  Fintype.card V→  
    ∀ errInner errDeep:ℝ,0≤  errDeep→  errInner≤  x*Fintype.card VP→  errDeep≤  x*Fintype.card VP→  
    let tailP:=fun e:EP=>e.val.1
    let headP:=fun e:EP=>e.val.2
    let ktailP:=fun e:KP=>e.val.1
    let kheadP:=fun e:KP=>e.val.2
    let SP:=Finset.univ.filter (fun z:VP×UP=>HP false z.1 z.2∨HP true z.1 z.2)
    let EI:={e:EP // tailP e∈I∧  headP e∈I}
    let KI:={e:KP // ktailP e∈I∧  kheadP e∈I}
    let tI:=fun e:EI=>(⟨tailP e.val,e.property.1⟩:I)
    let hI':=fun e:EI=>(⟨headP e.val,e.property.2⟩:I)
    let ktI:=fun e:KI=>(⟨ktailP e.val,e.property.1⟩:I)
    let khI:=fun e:KI=>(⟨kheadP e.val,e.property.2⟩:I)
    let H0Inner:=fun v:I=>fun u:J=>HP false v.val u.val
    let HKInner:=fun v:I=>fun u:J=>HP true v.val u.val
    (∀ v,|occurrenceDegree (Sum.elim tI ktI) v-
      (∑ u,if H0Inner v u then (1:ℝ) else 0)-(∑ u,if HKInner v u then (1:ℝ) else 0)|≤  etaBal*I.card)→  
    (∀ v,|occurrenceDegree (Sum.elim hI' khI) v-
      (∑ u,if H0Inner v u then (1:ℝ) else 0)-(∑ u,if HKInner v u then (1:ℝ) else 0)|≤  etaBal*I.card)→  
    (∀ v,|occurrenceDegree khI v-(∑ u,if HKInner v u then (1:ℝ) else 0)|≤  etaBal*I.card)→  
    (∀ u,|(∑ v,if H0Inner v u then (1:ℝ) else 0)-(r+4:ℕ)*(∑ v,if HKInner v u then (1:ℝ) else 0)|≤  etaBal*I.card)→  
    BipartiteLargeCut (occurrenceMultiplicity tI hI') deltaI (2*hIcut)→  
    BipartiteLargeCut (occurrenceMultiplicity ktI khI) deltaI (2*hIcut)→  
    BipartiteLargeCut (relationMultiplicity H0Inner) deltaI (2*hIcut)→  
    BipartiteLargeCut (relationMultiplicity HKInner) deltaI (2*hIcut)→  
    MarkedRemainderDivisible tailP headP ktailP kheadP (HP true) Finset.univ SP (r+4)→  
    (∀ z i,|markedFiniteDomainBalance tailP headP ktailP kheadP (HP true) Finset.univ SP (r+4) I J z i|≤  errInner)→  
    (∀ z i,|markedFiniteDomainBalance tailP headP ktailP kheadP (HP true) Finset.univ SP (r+4) T Wrem z i|≤  errDeep)→  
    ∃ E₀:Finset (Finset VP⊕(VP×UP)),
    ∃ N:Finset (MarkedWheel (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2)
      (r+4) πP (3*d) (HP false) (HP true)),
      (∀ Y∈N,∀ Y'∈N,Y≠Y'→  Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Y'))∧  
      let A':=Finset.univ\N.biUnion markedWheelArcs
      let S':=SP\N.biUnion markedWheelSpokePairs
      let B:=markedFiniteResources (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2) πP Finset.univ SP
      let L:=markedFiniteResources (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2) πP A' S'
      let removed:=B.filter (markedInnerResource I J)\L;
      MarkedRemainderDivisible (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2) (HP true) A' S' (r+4)∧  
      (∀ a∈A',Sum.elim (fun e:EP=>e.val.1) (fun e:KP=>e.val.1) a∈I∧  Sum.elim (fun e:EP=>e.val.2) (fun e:KP=>e.val.2) a∈I)∧  
      (∀ z∈S',z.1∈I∧  z.2∈J)∧  L=B\N.biUnion markedWheelPhysicalResources∧  
      removed.filter (markedStarResource T Wrem)=E₀∧  removed.filter (markedInnerResource T Wrem)=∅∧  
      (∀ physical z,(((markedIncidentEdges (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2)
        πP (HP false) (HP true) physical z).filter (fun e=>markedActivePhysical (fun e:EP=>e.val.1) (fun e=>e.val.2)
        (fun e:KP=>e.val.1) (fun e=>e.val.2) πP (HP false) (HP true) e∈removed)).card:ℝ)≤  6*x*I.card+4*(ν*Fintype.card (V⊕U)))∧  
      (∀ physical z,(((markedIncidentEdges (fun e:EP=>e.val.1) (fun e=>e.val.2) (fun e:KP=>e.val.1) (fun e=>e.val.2)
        πP (HP false) (HP true) physical z).filter (fun e=>markedActivePhysical (fun e:EP=>e.val.1) (fun e=>e.val.2)
        (fun e:KP=>e.val.1) (fun e=>e.val.2) πP (HP false) (HP true) e∈removed.filter (markedStarResource T Wrem))).card:ℝ)≤  6*x*I.card) :=by
  obtain ⟨c₀,hcover⟩:=marked_protected_cover_down_separate_geometry_from_packings gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  obtain ⟨kappaA,ξA,hkappaA,hξA,hcover⟩:=hcover r hr hrc rho omega t p0 betaA aLoA BA hrho hrho1 ho ho1 ht ht1 hPA0 hp0 hpr hpk hpt hbA haA hBA
  have hst:(((r+1)+3:ℕ):ℝ)*t≤  1:=by simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_ofNat] using ht1
  have hetaDeep:0<t*(t*omega/2)/64:=by positivity
  have hetaDeepSmall:t*(t*omega/2)/64≤  t*(t*omega/2)/32:=by linarith
  obtain ⟨epsDeep,hepsDeep,Kdeep,hKdeep,zetaDeep,hzetaDeep,thetaDeep,hThetaDeep,etaEmax,hEtaEmax,hdeep⟩:=
    marked_constructed_deep_canonical_estimates r hr omega t rho gamma (t*(t*omega/2)/64)
      ho ht hrho hrho1 hg hg1 hst hetaDeep hetaDeepSmall (min betaA (t/4)) aLoA BA p0
      (lt_min hbA (by positivity)) ((min_le_right _ _).trans (by linarith)) haA hBA.le hp0
  refine ⟨Kdeep,hKdeep,min kappaA epsDeep,min ξA zetaDeep,thetaDeep,lt_min hkappaA hepsDeep,lt_min hξA hzetaDeep,hThetaDeep,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  have hkA:=hkk.trans (min_le_left _ _)
  have hkD:=hkk.trans (min_le_right _ _)
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩:=hcover kappa hkappa hkA alphaInner omegaInner hAlpha hOmega hOmega1
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,?_⟩
  intro ν β aLo B hν hβ hBetaSmall haLo hB
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩:=hcover ν β aLo B hν hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,hcover⟩:=hcover p hp hp1 hpp
  obtain ⟨delta,hdelta,hcover⟩:=hcover Kdeep etaEmax hEtaEmax
  refine ⟨θ,hθ,min delta etaEmax,lt_min hdelta hEtaEmax,?_⟩
  intro x hx hxdelta omegaI hIcut deltaI hoI hhI hdI hdIs
  have hxd:=hxdelta.trans (min_le_left _ _)
  have hxe:=hxdelta.trans (min_le_right _ _)
  obtain ⟨etaBal,hetaBal,NI,hdeep⟩:=hdeep omegaI hIcut deltaI x hoI hhI hdI hdIs hx x hx hxe
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨NA,hNA,hcover⟩:=hcover x hx hxd d hd
  obtain ⟨ND,hND,hdeep⟩:=hdeep d hd
  refine ⟨max NA ND,le_max_of_le_left hNA,?_⟩
  intro VP UP W V U Gamma Color _ _ _ _ _ _ _ _ _ _ _ _ hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    pRef kRef DRef hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    EP KP hDeepConfigs hDeepLoad I J xiDeep hXi0 hXiScale hDeepGap hTI hWremJ hI hIsize hJsize hNI hJlow hJI hTcut hWcut hTdeep hWdeep
    f ρ hf P pr kr sr D τweight hDlo hDhi weight hw Zinner hdtypesP hsepP Q S g c X
    hXimage hZimage hrows0 hconfigs0 hload0
    errR0 errI0 heR0 heI0 hErrR hErrI hZlow hrowEnd0 hidxEnd0
    errParent heP hNearP hMinP hTinner hErrParent pA DA hinnerSize hX hVhalf
    errInner errDeep heDeep hErrInner hErrDeep tailP headP ktailP kheadP SP EI KI tI hI' ktI khI H0Inner HKInner
    hbp hbm hbk hbw hc0 hcK hcs0 hcsK hDivP hBalI hBalT
  have hNPA:NA≤  Fintype.card VP:=(le_max_left _ _).trans hnP
  have hNPD:ND≤  Fintype.card VP:=(le_max_right _ _).trans hnP
  have hNWA:NA≤  Fintype.card W:=(le_max_left _ _).trans hnW
  have hn0:0≤  (Fintype.card VP:ℝ):=Nat.cast_nonneg _
  have hError:kappa*Fintype.card VP≤  epsDeep*Fintype.card VP:=mul_le_mul_of_nonneg_right hkD hn0
  have hRowsDeep:MarkedRowsWithSpokes PP πP d ((r+1)+11) Finset.univ
      (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2) qP sP aP cP (epsDeep*Fintype.card VP) σP HP:=by
    have he:rho*((((r+1)+3:ℕ):ℝ)*t)/2=pRef:=by dsimp [pRef];push_cast;ring
    have hk:rho*t/2=kRef:=by
      dsimp [kRef,pRef]
      have hr4:(r+4:ℝ)≠0:=by positivity
      field_simp <;> ring
    rw [he,hk]
    intro SS TT JJ hSS hTT hJJ hinj
    exact (hrowsP SS TT JJ (by omega) (by omega) (by omega) hinj).trans_le hError
  have hIndicesDeep:MarkedIndicesWithSpokes πP d ((r+1)+11) Finset.univ qP sP aP cP (epsDeep*Fintype.card VP) σP HP:=by
    intro JJ hJJ hsep
    exact (hindicesP JJ (by omega) hsep).trans_le hError
  have hIsizeD:(I.card:ℝ)≤  zetaDeep*Fintype.card VP:=hIsize.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hJsizeD:(J.card:ℝ)≤  zetaDeep*Fintype.card VP:=hJsize.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hsr:((r+4:ℝ)*t)≤  1:=ht1
  have hpr1:pRef≤  1:=by
    have hh:=mul_le_mul_of_nonneg_left ht1 hrho.le
    dsimp [pRef]
    nlinarith only [hh,hrho1]
  have hkr1:kRef≤  1:=by
    have hk:kRef=rho*t/2:=by
      dsimp [kRef,pRef]
      have hr4:(r+4:ℝ)≠0:=by positivity
      field_simp <;> ring
    rw [hk]
    have htone:t≤  1:=by have hr0:0≤  (r:ℝ):=Nat.cast_nonneg _;nlinarith only [ht1,hr0,ht]
    have hh:=mul_le_mul_of_nonneg_left htone hrho.le
    nlinarith only [hh,hrho1]
  have hsrlo:p0≤  (r+4:ℝ)*t:=by
    have hr0:0≤  (r:ℝ):=Nat.cast_nonneg _
    nlinarith only [hpt,hr0,ht]
  have hkref:kRef=rho*t/2:=by
    dsimp [kRef,pRef]
    have hr4:(r+4:ℝ)≠0:=by positivity
    field_simp <;> ring
  obtain ⟨CAdelete,CSdelete,hCAD,hCSD,hCADdeg,hCSDrow,hCSDcol,havoid,hInnerDiv,
      ME,hME,hMEinner,hMER,hMEV,hMEU,hMEA,hMES,MD,hMD,hMDR,hMDV,hMDU,hMDinner,hMDstar,hMDRdisj,hMDSdisj,hDeepR,hDeepS,hActive⟩:=
    hdeep VP UP Gamma Color hNPD (Nat.cast_le.mpr hUP) hUPlow PP πP hPdeg
      (fun v=>(hPreg v).trans hError) qP sP aP cP hqP
      (by intro u;simpa only [Nat.add_assoc,Nat.reduceAdd,Nat.cast_add,Nat.cast_ofNat] using hsP u) σP HP hRowsDeep hIndicesDeep
      DRef tauRef pRef kRef ((r+4:ℝ)*t) hDloP hDhiP hpr (by rw [hkref];exact hpk) hsrlo hpr1 hkr1 hsr weightRef hwRef
      hDeepConfigs hDeepLoad (fun v u=>hdtypesP u v) hsepP I T J Wrem hTI hWremJ hI hT hIsizeD hJsizeD
      hNI hJlow hJI hTcut hWcut hbp hbm hbk hbw hc0 hcK hcs0 hcsK hDivP
  let CA:=(Finset.univ.filter (fun a:EP⊕KP=>Sum.elim tailP ktailP a∈I∧  Sum.elim headP kheadP a∈I))\CAdelete
  let CS:=(SP.filter (fun z=>z.1∈I∧  z.2∈J))\CSdelete
  let KA:=CA.filter (fun a=>Sum.elim tailP ktailP a∈T∨Sum.elim headP kheadP a∈T)
  let KS:=CS.filter (fun z=>z.1∈T∨z.2∈Wrem)
  let KR:=markedSampleArcSetGraph PP πP d σP KA
  let KSgraph:=markedFiniteSpokeGraph KS
  let E₀:=(markedFiniteResources tailP headP ktailP kheadP πP CAdelete CSdelete).filter (markedStarResource T Wrem)
  have hKA:∀ a∈KA,Sum.elim tailP ktailP a∈I∧  Sum.elim headP kheadP a∈I:=by
    intro a ha;exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1).2
  have hKS:∀ z∈KS,z.1∈I∧  z.2∈J:=by
    intro z hz;exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1).2
  obtain ⟨hKR,hKSgraph⟩:=marked_finite_inner_graph_support PP πP d σP I J hI KA KS hKA hKS
  have hDRprior:markedSampleArcSetGraph PP πP d σP (KA∪ME.biUnion markedWheelArcs)=KR⊔markedPackingRimGraph ME:=by
    rw [markedSampleArcSetGraph_union,markedSampleArcSetGraph_packing] <;> rfl
  have hDSprior:markedFiniteSpokeGraph (KS∪ME.biUnion markedWheelSpokePairs)=KSgraph⊔markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs):=by
    rw [markedFiniteSpokeGraph_union] <;> rfl
  rw [hDRprior] at hMDRdisj hDeepR
  rw [hDSprior] at hMDSdisj hDeepS
  have hE₀:∀ z,((E₀.filter (markedPhysicalIncident z)).card:ℝ)≤  3*(x*I.card):=by
    intro z
    apply marked_finite_correction_restricted_incidence tailP headP ktailP kheadP πP CAdelete CSdelete (x*I.card)
      (mul_nonneg hx.le (Nat.cast_nonneg _)) _ _ _ (markedStarResource T Wrem) z
    · intro v;simpa only [eq_comm] using hCADdeg v
    · intro v;simpa only [eq_comm] using hCSDrow v
    · exact hCSDcol
  have hE₀star:∀ e∈E₀,markedStarResource T Wrem e:=fun e he=>(Finset.mem_filter.mp he).2
  have hE₀deep:E₀.filter (markedInnerResource T Wrem)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have he':e∈(markedFiniteResources tailP headP ktailP kheadP πP CAdelete CSdelete).filter (markedInnerResource T Wrem):=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,(Finset.mem_filter.mp he).2⟩
    rw [havoid] at he';exact Finset.notMem_empty _ he'
  have hXpre:∀ v,fA v∈I↔v∈X:=by
    intro v
    have hnot:fA v∉T:=by
      have hh:fA v∈Finset.univ.image fA:=Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
      rw [hfX] at hh;exact (Finset.mem_sdiff.mp hh).2
    have he:fA v∈X.image fA↔v∈X:=by
      constructor
      · intro h;obtain ⟨w,hw,he⟩:=Finset.mem_image.mp h;exact fA.injective he ▸ hw
      · intro h;exact Finset.mem_image.mpr ⟨v,h,rfl⟩
    rw [hXimage] at he
    simpa only [Finset.mem_sdiff,hnot,not_false_eq_true,and_true] using he
  have hZpre:∀ u,gA u∈J↔u∈Zinner:=by
    intro u
    have hnot:gA u∉Wrem:=by
      have hh:gA u∈Finset.univ.image gA:=Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
      rw [hgX] at hh;exact (Finset.mem_sdiff.mp hh).2
    have he:gA u∈Zinner.image gA↔u∈Zinner:=by
      constructor
      · intro h;obtain ⟨v,hv,he⟩:=Finset.mem_image.mp h;exact gA.injective he ▸ hv
      · intro h;exact Finset.mem_image.mpr ⟨u,h,rfl⟩
    rw [hZimage] at he
    simpa only [Finset.mem_sdiff,hnot,not_false_eq_true,and_true] using he
  obtain ⟨hOutside,hBalance⟩:=hActive V U fA gA π hcomm
    (by intro v;rw [hfX];simp only [Finset.mem_sdiff,Finset.mem_univ,true_and])
    (by intro u;rw [hgX];simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]) X Zinner hXpre hZpre
  have hInnerOrder:(I.card:ℝ)≤  Fintype.card VP:=Nat.cast_le.mpr (Finset.card_le_univ I)
  have hInnerSizeA:((ordinaryInnerVertices X Zinner).card:ℝ)≤  ξA*Fintype.card V:=
    hinnerSize.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  let DRactive:=markedPackingRimGraph ME⊔markedPackingRimGraph MD
  let DSactive:=markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)
  let edges:=@SimpleGraph.edgeFinset VP DRactive (@SimpleGraph.fintypeEdgeSet VP DRactive inferInstance (fun v w=>Classical.propDecidable (DRactive.Adj v w)))
  let oldσ:=rawMarkedRestrictPair fA gA (rawMarkedDeleteRims σP (markedPackingRimGraph ME⊔markedPackingRimGraph MD).edgeFinset)
  let newσ:=rawMarkedRestrictPair fA gA (rawMarkedDeleteRims σP edges)
  let HA:=fun b v u=>markedDeletePhysicalSpokes HP DSactive b (fA v) (gA u)
  have heEdges:(markedPackingRimGraph ME⊔markedPackingRimGraph MD).edgeFinset=edges:=by
    apply Finset.coe_injective
    simp only [edges,SimpleGraph.coe_edgeFinset,DRactive]
  have heσ:oldσ=newσ:=by dsimp only [oldσ,newσ];rw [heEdges]
  have hOutsideA:=(marked_sample_outside_balance_congr P π d (r+4) oldσ newσ HA HA heσ rfl X Zinner).mp hOutside
  have hBalancesActual:=fun z i=>hBalance errInner errDeep heDeep hBalI hBalT z i
  have hBalancesNew:=fun z i=>by
    have hh:=hBalancesActual z i
    obtain ⟨hfull,hinner⟩:=marked_sample_finite_balance_congr P π d (r+4) oldσ newσ HA HA heσ rfl X Zinner z i
    rw [hfull,hinner] at hh
    exact hh
  have hC:=hcover VP UP W V U Gamma Color hNPA hUP hUPlow hNWA hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
  have hC:=hC I J x xiDeep hx.le hXi0 le_rfl hXiScale hDeepGap hWremJ hTdeep hWdeep ME MD hMER hMEV hMEU hMDstar hMDR hMDV hMDU
  have hC:=hC DRactive DSactive rfl rfl
  have hC:=hC f ρ hf D τweight hDlo hDhi weight hw Zinner hdtypesP hsepP hXimage hZimage hrows0 hconfigs0 hload0
    errR0 errI0 heR0 heI0 hErrR hErrI hZlow hrowEnd0 hidxEnd0
  have hC:=hC errParent heP hNearP hMinP hTinner hErrParent hInnerSizeA hX
  have hC:=hC I.card x errInner errDeep hVhalf hInnerOrder hx.le hErrInner hErrDeep le_rfl
  have hC:=hC hBalancesNew
  have hC:=hC hOutsideA
  have hC:=hC hME hMD hDivP hI
  have hC:=hC KR KSgraph hKR hKSgraph hMDRdisj hMDSdisj
  obtain ⟨N,hN,hDivN,hAN,hSN,hRem,hStar,hDeep,hInc,hStarInc⟩:=hC (3*(x*I.card)) E₀ (mul_nonneg (by norm_num) (mul_nonneg hx.le (Nat.cast_nonneg _))) hE₀ hMEinner hMDinner hE₀star hE₀deep hDeepR hDeepS
  refine ⟨E₀,N,hN,hDivN,hAN,hSN,hRem,hStar,hDeep,?_,?_⟩
  · intro physical z
    convert hInc physical z using 1 <;> ring
  · intro physical z
    convert hStarInc physical z using 1 <;> ring

end Oberwolfach
