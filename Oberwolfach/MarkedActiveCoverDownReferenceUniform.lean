module

public import Oberwolfach.MarkedActiveCoverDownReference
public import Oberwolfach.MarkedActiveGlobalReferenceUniform
public import Oberwolfach.MarkedActiveCoverDownCanonicalUniformSpoke

@[expose] public section
/-! The parent-reference and active cover-down constants are chosen before
actual density values. All profiles, weights and degree targets retain their
actual values. The endpoint class lower bounds remain explicit inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 60000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_cover_down_reference_uniform_densities (gamma pA0:ℝ)
    (hg:0<gamma) (hg1:gamma≤1) (hpA0:0<pA0) (hpA01:pA0≤1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤r→ c₀≤r+5→ ∀ rho₀ omega₀ t₀ p0 betaA aLoA BA:ℝ,
    0<rho₀ → 0<omega₀ → 0<t₀ → 0<p0 → p0≤1/2 → 0<betaA → 0<aLoA → 0<BA →
    ∃ kappa0 ξ:ℝ,0<kappa0∧0<ξ∧∀ kappa:ℝ,0<kappa→ kappa≤kappa0→
    ∀ βfree ν β aLo B pstar a gap omegaInner:ℝ,
    0<βfree→0<ν→0<β→0<aLo→0≤B→0<pstar→0<a→a≤1→0<gap→0<omegaInner→ omegaInner≤1→
    ∃ η ηEnd ζ pmax:ℝ,0<η∧0<ηEnd∧0<ζ∧0<pmax∧pmax≤1/8∧
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤1),p≤pmax→ ∃ θ:ℝ,0<θ∧∀ d:ℕ,1≤d→∃ N:ℕ,1≤N∧
    ∀ rho omega t:ℝ,
    rho₀≤rho → rho≤1 → omega₀≤omega → omega≤1 → t₀≤t → (r+4:ℝ)*t≤1 →
    pA0≤rho*(r+4:ℝ)*t/2 → p0≤rho*(r+4:ℝ)*t/2 → p0≤rho*t/2 → p0≤t →
    ∀ (VP UP W V U Gamma Color:Type) [Fintype VP] [Fintype UP] [LinearOrder VP] [DecidableEq UP]
      [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color],
    N≤Fintype.card VP→ Fintype.card UP≤Fintype.card VP→ omega*Fintype.card VP≤(Fintype.card UP:ℝ)→ 
    N≤Fintype.card W→ omegaInner*Fintype.card (V⊕U)≤(Fintype.card W:ℝ)→ 
    ∀ (fA:V↪oVP) (gA:U↪UP) (PP:SimpleGraph VP) (πP:Equiv.Perm VP) (π:Equiv.Perm V),
    (∀ x,fA (π x)=πP (fA x))→ 
    ∀ (T:Finset VP) (Wrem:Finset UP),(∀ x,πP x∈T↔x∈T)→ 
    Finset.univ.image fA=Finset.univ\T→ Finset.univ.image gA=Finset.univ\Wrem→ 
    (T.card:ℝ)≤kappa*Fintype.card VP→ (Wrem.card:ℝ)≤kappa*Fintype.card VP→ 
    (∀ x,(1/2+gamma/2)*Fintype.card VP≤(PP.degree x:ℝ))→ 
    (∀ x,|(PP.degree x:ℝ)-2*Fintype.card UP/rho|≤kappa*Fintype.card VP)→ 
    ∀ (qP:UP→ Gamma→ ℝ) (sP:UP→ Color→ ℝ) (aP:Gamma) (cP:Color),
    (∀ u,qP u aP=t)→ (∀ u,sP u cP=(r+4:ℝ)*t)→ 
    ∀ (σP:RawMarkedOutcome VP UP Gamma Color) (HP:Bool→ VP→ UP→ Prop),
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
    (Fintype.card VP:ℝ)/2≤DRef→ DRef≤2*Fintype.card VP→ 
    ∀ (tauRef:ℝ) (weightRef:(Fin (r+4+1)→ VP)→ ℝ),SuccessorSequenceWeightConditions PP πP (3*d) DRef tauRef aLoA BA weightRef→ 
    (let seed:=fun C:MarkedWheel (Prod.fst:VP×VP→ VP) Prod.snd Prod.fst Prod.snd (r+4) πP (3*d)
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
    ∀ (D τweight pr kr sr:ℝ),
    (Fintype.card W:ℝ)/2≤D→ D≤2*Fintype.card W→ 
    pstar≤pr→ pstar≤kr→ pstar≤sr→ pr≤1→ kr≤1→ sr≤1→ 
    ∀ weight:(Fin (r+4+1)→ W)→ ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight→ 
    ∀ Zinner:Finset U,
    (∀ u v,¬(H false v u∧H true v u))→ 
    (∀ u v z,H false v u→ H true z u→ v≠π z)→ 
    ∀ (Q:U→ Gamma→ ℝ) (S:U→ Color→ ℝ) (g:Gamma) (c:Color),
    (∀ u,Q u g=t)→ 
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
    ∀ h:ℕ,3≤h→ ∀ errR errI:ℝ,0≤errR→ 0≤errI→ 
      2*errR≤ηEnd*(a*Fintype.card (V⊕U))→ 2*errI≤ηEnd*(a*Fintype.card (V⊕U))→ 
    MarkedRowsWithSpokes P π d h X pr kr Q S g c errR σ H→ 
    MarkedIndicesWithSpokes π d h Zinner Q S g c errI σ H→ 
    ∀ w:Bool→ ℝ,(∀ u∈Zinner,Q u g=w true)→ (∀ u∈Zinner,S u c=w false)→ 
      (∀ e,p0≤w e∧w e≤1)→ 
    (∀ v∉X,∀ j:Fin 5,
      a*Fintype.card (V⊕U)≤((markedEndpointLabels P π d X
        (markedEndpointFiveRimType j,markedEndpointFiveIncoming j,v) σ).card:ℝ)∧
      a*Fintype.card (V⊕U)≤((Zinner.filter (H (markedEndpointFiveRootSpokeType j) v)).card:ℝ))→ 
    (∀ v∉X,((markedEndpointLabels P π d X (true,false,v) σ).card:ℝ)+
      gap*Fintype.card (V⊕U)≤(Zinner.filter (H false v)).card)→ 
      MarkedBoundaryExtensionCounts tail head ktail khead (H false) (H true) X (β*Fintype.card (V⊕U))→ 
    let pA:=rho*(r+4:ℝ)*t/2
    let DA:=2*Fintype.card U/rho;
    ( (ordinaryInnerVertices X Zinner).card:ℝ)≤ξ*Fintype.card V → 
    (∀ x,π x∈X↔x∈X) → 
    (∀ j x u,βfree*Fintype.card (V⊕U)≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then (H true) z u else (H false) z u))).card:ℝ)) → 
    (∀ j x y u,x≠(if j then π y else y)→ βfree*Fintype.card (V⊕U)≤
      ((X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧(H false) z u)).card:ℝ)) → 
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→ Sum.elim head khead a∉X→ 
      ¬PermutationClose π (3*d) (Sum.elim tail ktail a) (Sum.elim head khead a)) → 
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→ Sum.elim head khead a∉X→ 
      βfree*Fintype.card (V⊕U)≤((Zinner.filter (fun u=>(H false) (Sum.elim tail ktail a) u∧
      (if markedArcType a then (H true) (Sum.elim head khead a) u else (H false) (Sum.elim head khead a) u))).card:ℝ)) → 
    let a:=fun r j=>((markedBalanceTermSet tail head ktail khead (H false) (H true) r j).card:ℝ)
    let c:=fun r j=>(((markedBalanceTermSet tail head ktail khead (H false) (H true) r j).filter (fun e=>
      (if markedActiveAuxTail tail ktail (H false) (H true) e=r then markedActiveAuxHead head khead (H false) (H true) e
        else markedActiveAuxTail tail ktail (H false) (H true) e)∈ordinaryInnerVertices X Zinner)).card:ℝ);
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (r+4) (a (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) → 
    (∀ (v:V) (i:Fin 3),|markedSixDegreeBalance (r+4) (c (Sum.inl v)) i.castSucc|≤θ*Fintype.card V) → 
    (∀ u,|markedSixDegreeBalance (r+4) (a (Sum.inr u)) 3|≤θ*Fintype.card V) → 
    (∀ u,|markedSixDegreeBalance (r+4) (c (Sum.inr u)) 3|≤θ*Fintype.card V) → 
    MarkedOutsideBalance tail head ktail khead (H true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) X Zinner→ 
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
       (∀ W∈M,∀ W'∈M,W≠W'→ Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
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
  obtain ⟨c₀,hcover⟩:=marked_active_cover_down_canonical_roots_uniform_spoke (gamma/8) pA0 (by positivity)
    (by linarith only [hg1]) hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho₀ omega₀ t₀ p0 betaA aLoA BA hrho₀ ho₀ ht₀ hp0 hp01 hbA haA hBA
  let delta:=min (min gamma p0) t₀/256
  let hcut:=min (gamma*p0) t₀/128
  have hdelta:0<delta:=by dsimp [delta];positivity
  have hhcut:0<hcut:=by dsimp [hcut];positivity
  have hdeltaMax:delta/2<1/4:=by
    have hh:min (min gamma p0) t₀≤1:=(min_le_left _ _).trans ((min_le_left _ _).trans hg1)
    dsimp [delta];linarith only [hh]
  obtain ⟨eps,eta0,delta0,ξ,he,heta0,hd0,hξ,hcover⟩:=hcover r hr hrc betaA (max 1 (1/p0))
    ((aLoA/2)/2^(r+4)) (2*BA/p0^(2*(r+4)+1)) (omega₀/2) hcut (delta/2)
    hbA (le_max_left _ _) (by positivity) (by positivity) (by positivity) hhcut (by positivity) hdeltaMax
  obtain ⟨kappa0,hkappa0,hglobal⟩:=marked_active_global_reference_conditions_uniform r (r+12) (by omega)
    rho₀ gamma omega₀ t₀ p0 betaA aLoA BA eps eta0 delta0 hrho₀ hg ho₀ ht₀ hp0 hbA haA hBA.le he heta0 hd0
  refine ⟨kappa0,ξ,hkappa0,hξ,?_⟩
  intro kappa hkappa hkk βfree ν β aLo B pstar a gap omegaInner hβfree hν hβ haLo hB hpstar ha ha1 hgap homega homega1
  obtain ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,hcover⟩:=hcover βfree ν β aLo B pstar t₀ p0 a gap omegaInner
    hβfree hν hβ haLo hB hpstar ht₀ hp0 (by linarith only [hp01]) ha ha1 hgap homega homega1
  refine ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,hcover⟩:=hcover p hp hp1 hpp
  refine ⟨θ,hθ,?_⟩
  intro d hd
  obtain ⟨NC,hNC,hcover⟩:=hcover d hd
  obtain ⟨NG,hNG,hglobal⟩:=hglobal kappa hkappa hkk d
  refine ⟨max NC NG,hNC.trans (le_max_left _ _),?_⟩
  intro rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt
  have hrho:0<rho:=hrho₀.trans_le hρ
  have ho:0<omega:=ho₀.trans_le hω
  have ht:0<t:=ht₀.trans_le htlo
  intro VP UP W V U Gamma Color _ _ _ _ _ _ _ _ _ _ _ _ hnP hUP hUPlow hnW hWlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    pRef kRef DRef hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef
    DR DS hrimD hrowD hcolD σ H
    f ρ hf P D τweight pr kr sr hDlo hDhi hprI hkrI hsrI hpr1 hkr1 hsr1 weight hw Zinner hdtypes hsep
    Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
    h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob hsize hgapParent
    Qext pA DA hinnerSize hX hstep hjoin hsepOutside hhubsOutside a₀ c₁ ha₀ hc₁ hau hcu hdiv
  have hglobalActual:=hglobal rho omega t hρ hrho1 hω ho1 htlo ht1 hpr hpk hpt VP UP V U Gamma Color ((le_max_right _ _).trans hnP) hUP hUPlow
    fA gA PP πP π hcomm T Wrem hT hfX hgX hTsize hWsize hPdeg hPreg qP sP aP cP hqP hsP σP HP
    hstats hcuts hconfigsP hrowsP hindicesP hrowOld hcolOld hDloP hDhiP tauRef weightRef hwRef hloadRef DR DS hrimD hrowD hcolD
  have hpAmax:pA≤1/2:=by
    have hh:=mul_le_mul_of_nonneg_left ht1 hrho.le
    dsimp [pA]
    nlinarith only [hh,hrho1]
  have hglobalFixed:MarkedActiveGlobalConditions tail head ktail khead π d r (H false) (H true)
      pA DA (gamma/8) betaA (max 1 (1/p0)) ((aLoA/2)/2^(r+4))
      (2*BA/p0^(2*(r+4)+1)) (omega₀/2) eps eta0 delta0 (delta/2) hcut:=by
    refine {hglobalActual with hubs_lower:=?_}
    have hh:=mul_le_mul_of_nonneg_right hω (show (0:ℝ)≤Fintype.card V by positivity)
    linarith only [hh,hglobalActual.hubs_lower]
  exact hcover t htlo W V U Gamma Color ((le_max_left _ _).trans hnW) hWlow f ρ π hf P D τweight pr kr sr
    hDlo hDhi hprI hkrI hsrI hpr1 hkr1 hsr1 weight hw σ H Zinner hdtypes hsep
    Q S g c hQ hrows hconfigs hload h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd
    w hQw hSw hwprob hsize hgapParent Qext pA DA hPA0 hpAmax hglobalFixed
    hinnerSize hX hstep hjoin hsepOutside hhubsOutside ha₀ hc₁ hau hcu hdiv

end Oberwolfach
