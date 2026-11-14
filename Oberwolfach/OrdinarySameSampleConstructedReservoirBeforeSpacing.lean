module

public import Oberwolfach.OrdinarySameSampleReservoirCorrectionEarlyGeometry
public import Oberwolfach.OrdinaryProtectedReservoirHighProbabilityBeforeSpacing
public import Oberwolfach.TwoComponentLower

@[expose] public section
/-! Apply the original uniform absorber probability theorem to construct the
protected reservoir and its correction together with any earlier event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_constructed_reservoir_before_spacing
    (r:ℕ) (hr:3≤r) (α pstar ω:ℝ)
    (hα:0<α) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω):
    ∃δ h εabs εv:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
    ∀(d:ℕ) (hd:2≤d),∀L:ℝ,0≤L→∀ξ:ℝ,∀hξ:0<ξ,∀hξh:ξ≤h/100,
    ∀m:ℕ,∃a b:ℕ,∀t f q₀:ℕ,∃N:ℕ,1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀(P F:SimpleGraph V) (D:ℕ),P.IsRegularOfDegree D→0<D→
      (cycleThreshold r+α)*Fintype.card V≤D→(∀v,(F.degree v:ℝ)≤L)→
    ∀(π:Equiv.Perm V),permutationConflictGraph π (3*d)≤F→
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),pstar≤2*p→pstar≤pH→pH≤1→
      2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color),(∀w,s w j=pH)→
    ∀(A Z Wterm W:Finset V) (Bterm B:Finset U),
      A=Finset.univ\Z→(Z.card:ℝ)≤εabs*Fintype.card V→
      Wterm.card+Bterm.card≤t→Wterm⊆W→Bterm⊆B→W.card≤f→
      (B.card:ℝ)≤εabs*Fintype.card V+f→
      (Z.card:ℝ)≤εv*Fintype.card V→(B.card:ℝ)≤εv*Fintype.card V+f→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (lossE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-lossE≤((μ.sigma ρ).prod ν).probability E→
    1-lossE-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)≤
      ((μ.sigma ρ).prod ν).probability (fun z=>E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B):=by
  let αg:ℝ:=min (α/2) (1/4:ℝ)
  have hαg:0<αg:=lt_min (by positivity) (by norm_num)
  have hαg1:αg≤1/2:=(min_le_right _ _).trans (by norm_num)
  have hαgα:αg≤α:=(min_le_left _ _).trans (by linarith)
  obtain ⟨δ,h,εv,ζ,hδ,hδsmall,hh,hεv,hζ,hζh,hcombine⟩:=ordinary_same_sample_reservoir_correction_probability_early_geometry r hr αg pstar ω
    hαg hαg1 hpstar hpstar1 hω
  obtain ⟨εabs,εtrans,hεabs,hεtrans,hreservoir⟩:=
    ordinary_uniform_protected_reservoir_high_probability_before_spacing r hr α pstar pstar ω
      hα hpstar hpstar hpstar1 hω
  refine ⟨δ,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,?_⟩
  intro d hd L hL ξ hξ hξh
  obtain ⟨εhost,hεhost,hreservoir⟩:=hreservoir d hd L hL
  obtain ⟨εsample,hεsample,hcombine⟩:=hcombine ξ hξ hξh
  intro m
  obtain ⟨a,b,taux,htaux,hreservoir⟩:=hreservoir m
  refine ⟨a,b,?_⟩
  intro t f q₀
  obtain ⟨Nr,hreservoir⟩:=hreservoir t f
  obtain ⟨Nc,hNc,hcombine⟩:=hcombine L hL d q₀ hd m t f a b
  let N:=max Nr Nc
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hωn hUn P F D hreg hD hdegree hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall R _ ρ E lossE μ ν hE
  have hnpos:0<Fintype.card V:=by dsimp [N] at hn;omega
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have hhalf:(1/2:ℝ)≤cycleThreshold r:=(cycleThreshold_half_le hr)
  have hGlobal:∀v,(1/2+αg)*Fintype.card V≤(P.degree v:ℝ):=by
    intro v
    rw [hreg v]
    exact (mul_le_mul_of_nonneg_right (show (1/2+αg:ℝ)≤cycleThreshold r+α by linarith) hn0).trans hdegree
  have hDlo:(Fintype.card V:ℝ)/2≤D:=by
    have hh':=(mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤cycleThreshold r+α by linarith) hn0).trans hdegree
    nlinarith only [hh']
  have hDhi:(D:ℝ)≤2*Fintype.card V:=by
    obtain ⟨v⟩:=Fintype.card_pos_iff.mp hnpos
    have hdv:=P.degree_lt_card_verts v
    rw [hreg v] at hdv
    have hdv':(D:ℝ)≤Fintype.card V:=by exact_mod_cast hdv.le
    linarith only [hdv',hn0]
  have hnear:∀v,|(P.degree v:ℝ)-(D:ℝ)|≤εhost*Fintype.card V:=by
    intro v
    rw [hreg v]
    simp only [sub_self,abs_zero]
    positivity
  have hp2:0≤2*p:=by positivity
  have hp21:2*p≤1:=by linarith
  let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>hp2) (fun _=>hp21) d hd q hq hQ s hs hS)
  have hRes:1-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)≤μraw.probability
      (fun raw=>OrdinaryUniformProtectedReservoirEvent r m t f a b εabs (rawWheelGraph P raw\F) F (rawWheelSpokes π d raw j)):=by
    have hh':=hreservoir V U Γ Color (by dsimp [N] at hn;omega) hUn hωn P F π hconf hnoshort hF
      (by intro v;rw [hreg v];exact hdegree) (D:ℝ) hDlo hDhi hnear (2*p) hpR hp21 q hq hQ s hs hS j
      (by intro w;rw [hj w];exact hpH) (by intro w;rw [hj w];exact hpH1) pH hpH hj
    convert hh' using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
  have hout:=hcombine V U Γ Color (by dsimp [N] at hn;omega) hωn hUn P F D hreg hD hGlobal hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpEq q hq hQ s hs hS j hj
    εabs A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall ρ E lossE
    (1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2) hE hRes
  convert hout using 1 <;> congr! 40
end Oberwolfach
