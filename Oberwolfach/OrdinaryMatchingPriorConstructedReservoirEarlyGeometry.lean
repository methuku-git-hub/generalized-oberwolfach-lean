module

public import Oberwolfach.OrdinarySameSampleConstructedReservoirEarlyGeometry
public import Oberwolfach.FiniteProductRegrouping
public import Oberwolfach.OrdinarySameSampleReservoirCorrectionEarlyGeometry
public import Oberwolfach.OrdinaryProtectedReservoirHighProbability
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

theorem ordinary_matching_prior_constructed_reservoir_probability_early_geometry
    (r d:ℕ) (hr:3≤r) (hd:2≤d) (α pstar ω L:ℝ)
    (hα:0<α) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω) (hL:0≤L):
    ∃δ h εabs εv:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
    ∀ξ:ℝ,∀hξ:0<ξ,∀hξh:ξ≤h/100,
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
      (E:(Σσ,R σ)→Prop) (lossE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-lossE≤(μ.sigma ρ).probability E→
    1-lossE-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)≤
      ((μ.sigma ρ).prod ν).probability (fun z=>E z.1 ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B):=by
  obtain ⟨δ,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,hmain⟩:=
    ordinary_same_sample_constructed_reservoir_probability_early_geometry r d hr hd α pstar ω L hα hpstar hpstar1 hω hL
  refine ⟨δ,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,?_⟩
  intro ξ hξ hξh m
  obtain ⟨a,b,hmain⟩:=hmain ξ hξ hξh m
  refine ⟨a,b,?_⟩
  intro t f q₀
  obtain ⟨N,hN,hmain⟩:=hmain t f q₀
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hωn hUn P F D hreg hD hdegree hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall R _ ρ E lossE μ ν hE
  have hpPrior:1-lossE≤((μ.sigma ρ).prod ν).probability (fun z=>E z.1):=by
    rw [finiteLaw_prod_first_probability]
    exact hE
  exact hmain V U Γ Color hn hωn hUn P F D hreg hD hdegree hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall ρ (fun z=>E z.1) lossE hpPrior
end Oberwolfach
