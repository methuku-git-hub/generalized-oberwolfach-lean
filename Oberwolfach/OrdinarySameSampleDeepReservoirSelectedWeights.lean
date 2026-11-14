module

public import Oberwolfach.OrdinarySameSampleReservoirSelectedCostWeights
public import Oberwolfach.OrdinaryExpandedVortexDeepRowsCutsRegular

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

theorem ordinary_same_sample_deep_reservoir_selected_weights
    (m d:ℕ) (hm:3  ≤  m) (hd:2  ≤  d) (α pmin ω ρ₀:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hpmin1:pmin  ≤  1) (hω:0<ω) (hρ₀:0<ρ₀):
    ∃loadK:ℕ,0<loadK ∧ ∃aDeep εDeep ρDeep θDeep:ℝ,0<aDeep ∧ 0<εDeep ∧ 0<ρDeep ∧ 0<θDeep ∧
    ∃c C δ h εabs εv:ℝ,0<c ∧ 0<C ∧ 0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
    ∀(ε ξ bHub Bweight ηHub Kdom χ χdeep eParent hParent:ℝ),
      0<ε   →   ε<1/4   →   ε≤aDeep   →   ε≤ρ₀/16   →   0<ξ   →   0<χ   →   0<χdeep   →  
      2/ε  ≤  Kdom   →   1+1/(ε/2)+1/((ε/2)*(ρ₀/8))  ≤  Kdom   →  
      bHub  ≤  c   →   (4*C/pmin^(3*m+1))*Kdom^m  ≤  Bweight   →   0<eParent   →   0<hParent   →  
    ∃tWeight eEvent hEvent cap rateGeo:ℝ,0<tWeight ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ 0<rateGeo ∧
      eEvent  ≤  eParent ∧ hEvent  ≤  hParent ∧
    ∀ξRes:ℝ,0<ξRes   →   ξRes  ≤  h/100   →   ∀mAbs:ℕ,∃aAbs bAbs:ℕ,∀tAbs fAbs q₀:ℕ,∃N:ℕ,1  ≤  N ∧
    ∀β:ℝ,0  ≤  β   →   β  ≤  1/4   →   β  ≤  α/8   →   β≤εDeep → ξ+2*β<ηHub   →
    ∀(εR εH χrows χcut aLoad:ℝ),0<εR → 0<εH → 0<χrows → 0<χcut → 0<aLoad → aLoad≤aDeep → ∃v₀:ℕ,1  ≤  v₀ ∧
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
      ((E z.1 ∧ OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryFixedVortexDeepCoverEvent m loadK d aDeep aLoad ρDeep θDeep P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin;
    let bound:ℝ:=1-(((lossE+χrows)+χdeep)+χcut)-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)-χ;
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
    bound ≤ ((μ.sigma ρ).prod ν).probability Good ∧
      (0<bound → ∃z,0<((μ.sigma ρ).prod ν).mass z ∧ Good z) :=by
  obtain ⟨loadK,hloadK,aDeep,εDeep,ρDeep,θDeep,haDeep,hεDeep,hρDeep,hθDeep,hdeep⟩:=
    ordinary_expanded_vortex_deep_rows_cuts_regular m hm α ρ₀ pmin hα hρ₀ hpmin hpmin1
  obtain ⟨c,C,δ,h,εabs,εv,hc,hC,hδ,hδ1,hh,hεabs,hεv,hboth⟩:=
    ordinary_same_sample_reservoir_selected_cost_weights m d hm hd α pmin ω hα hpmin hpmin1 hω
  refine ⟨loadK,hloadK,aDeep,εDeep,ρDeep,θDeep,haDeep,hεDeep,hρDeep,hθDeep,
    c,C,δ,h,εabs,εv,hc,hC,hδ,hδ1,hh,hεabs,hεv,?_⟩
  intro ε ξ bHub Bweight ηHub Kdom χ χdeep eParent hParent hε hε1 hεa hερ hξ hχ hχdeep hK hKdom hb hB he hhParent
  obtain ⟨tWeight,eEvent,hEvent,cap,rateGeo,ht,heEvent,hhEvent,hcap,hrateGeo,heBound,hhBound,hboth⟩:=
    hboth ε ρ₀ ξ bHub Bweight ηHub Kdom χ eParent hParent hε hε1 hρ₀ hξ hχ hK hKdom hb hB he hhParent
  refine ⟨tWeight,eEvent,hEvent,cap,rateGeo,ht,heEvent,hhEvent,hcap,hrateGeo,heBound,hhBound,?_⟩
  intro ξRes hξRes hξResCap mAbs
  obtain ⟨aAbs,bAbs,hboth⟩:=hboth ξRes hξRes hξResCap mAbs
  refine ⟨aAbs,bAbs,?_⟩
  intro tAbs fAbs q₀
  obtain ⟨N,hN,hboth⟩:=hboth tAbs fAbs q₀
  refine ⟨N,hN,?_⟩
  intro β hβ hβ1 hβα hβε hgap εR εH χrows χcut aLoad hεR hεH hχrows hχcut haLoad haLoadCap
  obtain ⟨vDeep,hvDeep,hdeep⟩:=hdeep ε χdeep hε hε1 hεa hερ hχdeep β hβ hβ1 hβα hβε
    εR εH χrows χcut hεR hεH hχrows hχcut aLoad haLoad haLoadCap d hd
  obtain ⟨vRes,hvRes,hboth⟩:=hboth β hβ hβ1 hβα hgap
  refine ⟨max vDeep vRes,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hωn hUn P F D vsize hreg hD hdegree hF hρlo hρhi hv Q π hπ hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq rateActual hrateActual hrateBound
  obtain ⟨weight,hweight,hboth⟩:=hboth V U Γ Color hn hωn hUn P F D vsize hreg hD hdegree hF hρlo hρhi
    (by omega) Q π hπ hconf hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq rateActual hrateActual hrateBound
  refine ⟨weight,hweight,?_⟩
  intro q hq hQ s hs hS j hj A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall R _ ρ E lossE μ ν hE αcut Prior bound Good
  have hnpos:0<Fintype.card V:=by omega
  have hhalf:1/2≤cycleThreshold (m+1):=cycleThreshold_half_le (by omega)
  have hprior:=hdeep V U Γ Color P D vsize hreg hnpos hρlo hρhi (by omega) Q π hπ hnoshort
    (cycleThreshold (m+1)) hhalf le_rfl hdegree p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    q hq hQ s hs hS j hj ρ E lossE hE
  change 1-(((lossE+χrows)+χdeep)+χcut)≤((μ.sigma ρ).prod ν).probability Prior at hprior
  have hout:=hboth (fun _=>cycleThreshold (m+1)+α-β/2)
    (fun i=>εR*(markedVortexInnerVertices Q i).card) (fun i=>εH*(markedVortexInnerHubs Q i).card)
    q hq hQ s hs hS j hj A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall
    ρ Prior (((lossE+χrows)+χdeep)+χcut) hprior
  simpa only [bound,Good] using hout
end Oberwolfach
