module

public import Oberwolfach.OrdinarySameSampleDeepTwoStepReservoirWeightsAllLevelsParent
public import Oberwolfach.OrdinaryJointReferenceAndInitialParentLoadCapSelector
public import Oberwolfach.OrdinaryExpandedVortexParentCommonWitness
public import Oberwolfach.OrdinaryVortexFullParentSelectionFromOriginal

@[expose] public section
/-! The corrected protected reservoir and the uniform adaptive hub-weight
 event can be required together on the same expanded outcome and fair coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_reference_joint_initial_parent_load_cap_all_levels
    (m d:ℕ) (hm:3  ≤  m) (hd:2  ≤  d) (α pmin ω ρ₀ ηP:ℝ)
    (hα:0<α) (hα1:α≤1)
    (hθ1:max (1/2) (cycleThreshold (m+1))+α/4≤1)
    (hpmin:0<pmin) (hpmin1:pmin  ≤  1) (hω:0<ω) (hρ₀:0<ρ₀) (hηP:0<ηP):
    ∃loadK:ℕ,0<loadK ∧ ∃aDeep εDeep ρDeep θDeep:ℝ,0<aDeep ∧ 0<εDeep ∧ 0<ρDeep ∧ 0<θDeep ∧
    ∃c C δ h εabs εv:ℝ,0<c ∧ 0<C ∧ 0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
    ∃(δref href βP row:ℝ) (kParent:ℕ) (βH cParent BParent εstar cLinear:ℝ),
      0<δref ∧ δref<1/4 ∧ 0<href ∧ 0<βP ∧ 0<row ∧ m+3≤kParent ∧
      0<βH ∧ 0<cParent ∧ 0<BParent ∧ 0<εstar ∧ 0<cLinear ∧
      OrdinaryGeneralDeepSafeCapacityRuleLinear m kParent hm (α/2) (ρ₀/16) (βH/8)
        (cParent*(1-δref)^((m+1)-1)) (BParent/((ρ₀/16)*pmin^(2*(m+1)-1))) (href/2) (δref/2) εstar cLinear ∧
      OrdinarySharedInitialParentLoadCapJointSelectorAt m loadK d hm (α/2) kParent ∧
    ∀(ε ξ bHub Bweight ηHub Kdom χ χdeep eParent hParent ηH χhost χref:ℝ),
      0<ε   →   ε<1/4   →   ε≤aDeep   →   ε≤ρ₀/16   →   0<ξ   →   0<χ   →   0<χdeep   →  
      2/ε  ≤  Kdom   →   1+1/(ε/2)+1/((ε/2)*(ρ₀/8))  ≤  Kdom   →  
      bHub  ≤  c   →   (4*C/pmin^(3*m+1))*Kdom^m  ≤  Bweight   →   0<eParent   →   0<hParent   →
      0<ηH → 0<χhost → 0<χref →  
    ∃tWeight eEvent hEvent cap rateGeo:ℝ,0<tWeight ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ 0<rateGeo ∧
      eEvent  ≤  eParent ∧ hEvent  ≤  hParent ∧
    ∃(εTri βmax:ℝ) (Mhost Mcut:ℕ),0<εTri ∧ 0<βmax ∧ βmax≤1/4 ∧ βmax≤α/8 ∧ βmax≤εTri ∧
      1≤Mhost ∧ 1≤Mcut ∧
    ∀ξRes:ℝ,0<ξRes   →   ξRes  ≤  h/100   →   ∀mAbs:ℕ,∃aAbs bAbs:ℕ,∀tAbs fAbs q₀:ℕ,∃N:ℕ,1  ≤  N ∧
    ∀β:ℝ,0  ≤  β   →   β  ≤  1/4   →   β  ≤  α/8   →   β≤εDeep → β≤βmax → ξ+2*β<ηHub   →
    ∀(εR εH χrows χcut χtwo aLoad:ℝ),0<εR → 0<εH → 0<χrows → 0<χcut → 0<χtwo → 0<aLoad → aLoad≤aDeep → ∃v₀:ℕ,1  ≤  v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
      N  ≤  Fintype.card V   →   ω*Fintype.card V  ≤  (Fintype.card U:ℝ)   →   Fintype.card U  ≤  Fintype.card V   →  
    ∀(P F:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D   →   0<D   →  
      (cycleThreshold (m+1)+α)*Fintype.card V  ≤  D   →   (∀v,(F.degree v:ℝ)  ≤  2*((3*d:ℕ):ℝ))   →  
      ρ₀  ≤  initialIndexDensity U D   →   initialIndexDensity U D  ≤  1   →   v₀  ≤  vsize   →  
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      permutationConflictGraph π (3*d)  ≤  F   →   (∀x l,0<l   →   l<2*d+1   →   (π^l) x≠x)   →  
    ∀(p k p₂ k₂ u:ℝ) (hp:0  ≤  p) (hk:0  ≤  k) (hp₂:0  ≤  p₂) (hk₂:0  ≤  k₂) (hu:0  ≤  u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u  ≤  1) (pH:ℝ),
      pmin  ≤  2*p   →   pmin  ≤  pH   →   pH  ≤  1   →   2*p=initialIndexDensity U D*pH   →  
    ∀rateActual:ℝ,0  ≤  rateActual  →  rateActual  ≤  rateGeo  →  
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
      ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)  →  ℝ,
    (∀i,i<Q.length   →   OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C bHub Bweight ηHub Kdom) ∧
    ∀(q:U  →  Γ  →  ℝ) (hq:∀w g,0  ≤  q w g) (hQ:∀w,∑g,q w g  ≤  1/8)
      (s:U  →  Color  →  ℝ) (hs:∀w j,0  ≤  s w j)
      (hS:∀w,∑j,s w j  ≤  intervalUncoveredProbability d (∑g,q w g)) (j:Color),
      (∀w,s w j=pH)   →  
    ∀(A Z Wterm W:Finset V) (Bterm B:Finset U),
      A=Finset.univ\Z   →   (Z.card:ℝ)  ≤  εabs*Fintype.card V   →  
      Wterm.card+Bterm.card  ≤  tAbs   →   Wterm⊆W   →   Bterm⊆B   →   W.card  ≤  fAbs   →  
      (B.card:ℝ)  ≤  εabs*Fintype.card V+fAbs   →  
      (Z.card:ℝ)  ≤  εv*Fintype.card V   →   (B.card:ℝ)  ≤  εv*Fintype.card V+fAbs   →  
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)  →  Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ) → Prop) (lossE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-lossE ≤ (μ.sigma ρ).probability E →
    let αcut:=min (α/4) (1/4:ℝ);
    let Prior:=fun z:(Σσ,R σ)×(Sym2 V→Bool)=>
      (((E z.1 ∧ OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryFixedVortexDeepCoverEvent m loadK d aDeep aLoad ρDeep θDeep P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin;
    let bound:ℝ:=1-((((lossE+χtwo)+χrows)+χdeep)+χcut)-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)-χ;
    let Good:=fun z=>Prior z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir (m+1) mAbs tAbs aAbs bAbs ξRes (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B ∧
      OrdinaryUniformEditWeightEvents Q π hπ m d (2*p) pH cap (eParent*ε) (hParent*ε)
        c (4*C/pmin^(3*m+1)) ηHub (fun _=>cycleThreshold (m+1)+α-β/2)
        (fun i=>εR*(markedVortexInnerVertices Q i).card) (fun i=>εH*(markedVortexInnerHubs Q i).card) s j raw ∧
      OrdinarySelectedCostWeightEvents Q π hπ m d (2*p) pH cap (eParent*ε) (hParent*ε)
        c (4*C/pmin^(3*m+1)) ηHub rateActual (fun _=>cycleThreshold (m+1)+α-β/2)
        (fun i=>εR*(markedVortexInnerVertices Q i).card) (fun i=>εH*(markedVortexInnerHubs Q i).card) s j raw;
    let L:=Q.length-1;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;
    let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ;
    let Fconf:=permutationConflictGraph π (3*d);
    ∃selection:OrdinaryGeneralFullDomainSelection m kParent d hm hd
      (max (1/2) (cycleThreshold (m+1))) (α/2) pmin (ρ₀/16) βP ηP row ηH βH cParent BParent εTri χhost (2*(3*d)) hpmin
      V U Γ Color (markedVortexVertexType Q) (markedVortexHubType Q) P Fconf f g ρi L,
    let Host:RawWheelOutcome V U Γ Color → Prop:=fun raw=>∀i ≤ L,
      ordinaryCombinedHostEvent m d kParent hm (P.comap (f i)) (Fconf.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold (m+1))) (α/2) pmin βP ηP row ηH βH cParent BParent (2*p) pH (selection.weight i)
        (fun z=>s (g i z)) j (ordinaryRawRestrictPair (f i) (g i) raw);
    let Cuts:RawWheelOutcome V U Γ Color×(Sym2 V → Bool) → Prop:=fun z=>∀i ≤ L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (Fconf.comap (f i)) (ρi i) d j δref href
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e));
    let All:=fun z=>Good z ∧ Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2);
    bound-χhost-χref ≤ ((μ.sigma ρ).prod ν).probability All ∧
      (0<bound-χhost-χref → ∃z,0<((μ.sigma ρ).prod ν).mass z ∧ All z) :=by
  obtain ⟨loadK,hloadK,aDeep,εDeep,ρDeep,θDeep,haDeep,hεDeep,hρDeep,hθDeep,
    c,C,δ,h,εabs,εv,hc,hC,hδ,hδ1,hh,hεabs,hεv,hboth⟩:=
    ordinary_same_sample_deep_two_step_reservoir_weights_all_levels_parent m d hm hd α pmin ω ρ₀ hα hpmin hpmin1 hω hρ₀
  have hαhalf:0<α/2:=by linarith
  have hαhalf1:α/2≤1/2:=by linarith
  have hθhalf:max (1/2) (cycleThreshold (m+1))+(α/2)/2≤1:=by linarith
  obtain ⟨δref,href,βP,row,kParent,βH,cParent,BParent,εstar,cLinear,
    hδref,hδref1,hhref,hβP,hrow,hk,hβH,hcParent,hBParent,hεstar,hcLinear,hrule,hjoint,hevents⟩:=
    ordinary_joint_reference_and_initial_parent_load_cap_selector m loadK d hm hd (α/2) ρ₀ pmin ηP
      hαhalf hαhalf1 hθhalf hρ₀ hpmin hpmin1 hηP
  refine ⟨loadK,hloadK,aDeep,εDeep,ρDeep,θDeep,haDeep,hεDeep,hρDeep,hθDeep,
    c,C,δ,h,εabs,εv,hc,hC,hδ,hδ1,hh,hεabs,hεv,
    δref,href,βP,row,kParent,βH,cParent,BParent,εstar,cLinear,
    hδref,hδref1,hhref,hβP,hrow,hk,hβH,hcParent,hBParent,hεstar,hcLinear,hrule,hjoint,?_⟩
  intro ε ξ bHub Bweight ηHub Kdom χ χdeep eParent hParent ηH χhost χref
    hε hε1 hεa hερ hξ hχ hχdeep hK hKdom hb hB he hhParent hηH hχhost hχref
  obtain ⟨tWeight,eEvent,hEvent,cap,rateGeo,ht,heEvent,hhEvent,hcap,hrateGeo,heBound,hhBound,hboth⟩:=
    hboth ε ξ bHub Bweight ηHub Kdom χ χdeep eParent hParent hε hε1 hεa hερ hξ hχ hχdeep hK hKdom hb hB he hhParent
  refine ⟨tWeight,eEvent,hEvent,cap,rateGeo,ht,heEvent,hhEvent,hcap,hrateGeo,heBound,hhBound,?_⟩
  obtain ⟨εTri,βmax,hεTri,hβmax,hβmax1,hβmaxα,hβTri,Mhost,Mcut,hMhost,hMcut,hselector,hcuts⟩:=
    hevents ηH ε χhost χref hηH hε (by linarith) hχhost hχref
  have hβmaxα':βmax≤α/8:=by linarith
  refine ⟨εTri,βmax,Mhost,Mcut,hεTri,hβmax,hβmax1,hβmaxα',hβTri,hMhost,hMcut,?_⟩
  have hboth:=hboth kParent Mhost Mcut βP ηP row ηH βH cParent BParent εTri χhost δref href χref hcuts hselector
  intro ξRes hξRes hξResCap mAbs
  obtain ⟨aAbs,bAbs,hboth⟩:=hboth ξRes hξRes hξResCap mAbs
  refine ⟨aAbs,bAbs,?_⟩
  intro tAbs fAbs q₀
  obtain ⟨N,hN,hboth⟩:=hboth tAbs fAbs q₀
  refine ⟨N,hN,?_⟩
  intro β hβ hβ1 hβα hβε hβmax' hgap εR εH χrows χcut χtwo aLoad hεR hεH hχrows hχcut hχtwo haLoad haLoadCap
  apply hboth β hβ hβ1 hβα hβε (hβmax'.trans hβTri) hgap εR εH χrows χcut χtwo aLoad hεR hεH hχrows hχcut hχtwo haLoad haLoadCap
end Oberwolfach
