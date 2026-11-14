module

public import Oberwolfach.OrdinarySameSampleReservoirUniformEditWeights
public import Oberwolfach.OrdinarySameSampleSelectedCostWeights

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

theorem ordinary_same_sample_reservoir_selected_cost_weights
    (m d:ℕ) (hm:3  ≤  m) (hd:2  ≤  d) (α pmin ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hpmin1:pmin  ≤  1) (hω:0<ω):
    ∃c C δ h εabs εv:ℝ,0<c ∧ 0<C ∧ 0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
    ∀(ε ρ₀ ξ bHub Bweight ηHub Kdom χ eParent hParent:ℝ),
      0<ε   →   ε<1/4   →   0<ρ₀   →   0<ξ   →   0<χ   →  
      2/ε  ≤  Kdom   →   1+1/(ε/2)+1/((ε/2)*(ρ₀/8))  ≤  Kdom   →  
      bHub  ≤  c   →   (4*C/pmin^(3*m+1))*Kdom^m  ≤  Bweight   →   0<eParent   →   0<hParent   →  
    ∃tWeight eEvent hEvent cap rateGeo:ℝ,0<tWeight ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ 0<rateGeo ∧
      eEvent  ≤  eParent ∧ hEvent  ≤  hParent ∧
    ∀ξRes:ℝ,0<ξRes   →   ξRes  ≤  h/100   →   ∀mAbs:ℕ,∃aAbs bAbs:ℕ,∀tAbs fAbs q₀:ℕ,∃N:ℕ,1  ≤  N ∧
    ∀β:ℝ,0  ≤  β   →   β  ≤  1/4   →   β  ≤  α/8   →   ξ+2*β<ηHub   →   ∃v₀:ℕ,1  ≤  v₀ ∧
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
    ∀(density tR tH:ℕ  →  ℝ) (q:U  →  Γ  →  ℝ) (hq:∀w g,0  ≤  q w g) (hQ:∀w,∑g,q w g  ≤  1/8)
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
      (E:(Σσ,R σ)×(Sym2 V  →  Bool)  →  Prop) (lossE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-lossE  ≤  ((μ.sigma ρ).prod ν).probability E   →  
    let bound:ℝ:=1-lossE-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)-χ;
    let Good:=fun z=>E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir (m+1) mAbs tAbs aAbs bAbs ξRes (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B ∧
      OrdinaryUniformEditWeightEvents Q π hπ m d (2*p) pH cap (eParent*ε) (hParent*ε)
        c (4*C/pmin^(3*m+1)) ηHub density tR tH s j raw ∧
      OrdinarySelectedCostWeightEvents Q π hπ m d (2*p) pH cap (eParent*ε) (hParent*ε)
        c (4*C/pmin^(3*m+1)) ηHub rateActual density tR tH s j raw;
    bound  ≤  ((μ.sigma ρ).prod ν).probability Good ∧
      (0<bound  →  ∃z,0<((μ.sigma ρ).prod ν).mass z ∧ Good z) :=by
  obtain ⟨c,C,δ,h,εabs,εv,hc,hC,hδ,hδ1,hh,hεabs,hεv,hboth⟩:=
    ordinary_same_sample_reservoir_uniform_edit_weights m d hm hd α pmin ω hα hpmin hpmin1 hω
  refine ⟨c,C,δ,h,εabs,εv,hc,hC,hδ,hδ1,hh,hεabs,hεv,?_⟩
  intro ε ρ₀ ξ bHub Bweight ηHub Kdom χ eParent hParent hε hε1 hρ₀ hξ hχ hK hKdom hb hB he hhParent
  obtain ⟨tWeight,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,hboth⟩:=
    hboth ε ρ₀ ξ bHub Bweight ηHub Kdom χ eParent hParent hε hε1 hρ₀ hξ hχ hK hKdom hb hB he hhParent
  obtain ⟨rateGeo,hrateGeo,hselect⟩:=ordinary_same_sample_selected_cost_weights ε ρ₀ cap d hε hε1 hρ₀ hcap
  refine ⟨tWeight,eEvent,hEvent,cap,rateGeo,ht,heEvent,hhEvent,hcap,hrateGeo,heBound,hhBound,?_⟩
  intro ξRes hξRes hξResCap mAbs
  obtain ⟨aAbs,bAbs,hboth⟩:=hboth ξRes hξRes hξResCap mAbs
  refine ⟨aAbs,bAbs,?_⟩
  intro tAbs fAbs q₀
  obtain ⟨N,hN,hboth⟩:=hboth tAbs fAbs q₀
  refine ⟨N,hN,?_⟩
  intro β hβ hβ1 hβα hgap
  obtain ⟨v1,hv1,hboth⟩:=hboth β hβ hβ1 hβα hgap
  obtain ⟨v2,hv2,hselect⟩:=hselect β hβ hβ1
  refine ⟨max v1 v2,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hωn hUn P F D vsize hreg hD hdegree hF hρlo hρhi hv Q π hπ hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq rateActual hrateActual hrateBound
  obtain ⟨weight,hweight,hboth⟩:=hboth V U Γ Color hn hωn hUn P F D vsize hreg hD hdegree hF hρlo hρhi
    (by omega) Q π hπ hconf hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
  refine ⟨weight,hweight,?_⟩
  intro density tR tH q hq hQ s hs hS j hj A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall
    R _ ρ E lossE μ ν hE bound Good
  have hnpos:0<Fintype.card V:=by omega
  have hhalf:1/2 ≤ cycleThreshold (m+1):=cycleThreshold_half_le (by omega)
  have hDhalf:(Fintype.card V:ℝ)/2 ≤ D:=by
    have hn0:(0:ℝ) ≤ Fintype.card V:=by positivity
    nlinarith [mul_nonneg hα.le hn0,mul_nonneg (show 0 ≤ cycleThreshold (m+1)-1/2 by linarith) hn0]
  let Res:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V → Bool) → Prop:=
    fun z=>let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir (m+1) mAbs tAbs aAbs bAbs ξRes (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B
  let σ:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V → Bool)=>
    fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
  have hprob:=hboth density tR tH q hq hQ s hs hS j hj A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall ρ E lossE hE
  change bound ≤ ((μ.sigma ρ).prod ν).probability (fun z=>E z ∧ Res z ∧
    OrdinaryUniformEditWeightEvents Q π hπ m d (2*p) pH cap (eParent*ε) (hParent*ε)
      c (4*C/pmin^(3*m+1)) ηHub density tR tH s j (σ z)) at hprob
  have hprob':bound ≤ ((μ.sigma ρ).prod ν).probability (fun z=>(E z ∧ Res z) ∧
    OrdinaryUniformEditWeightEvents Q π hπ m d (2*p) pH cap (eParent*ε) (hParent*ε)
      c (4*C/pmin^(3*m+1)) ηHub density tR tH s j (σ z)):=by
    apply hprob.trans
    apply finiteLaw_probability_mono
    intro z hz
    exact ⟨⟨hz.1,hz.2.1⟩,hz.2.2⟩
  have hout:=hselect V U Γ Color _ P D vsize hreg hnpos hDhalf hρlo hρhi (by omega) Q π hπ m (2*p) pH
    (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub density tR tH s j rateActual hrateActual hrateBound
    ((μ.sigma ρ).prod ν) (fun z=>E z ∧ Res z) σ bound hprob'
  simpa only [Good,Res,σ,and_assoc] using hout
end Oberwolfach
