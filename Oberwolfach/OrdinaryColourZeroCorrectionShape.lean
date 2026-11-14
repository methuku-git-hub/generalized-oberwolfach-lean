module

public import Oberwolfach.OrdinaryColourZeroOnPrior
public import Oberwolfach.OrdinaryMatchingPriorConstructedReservoirEarlyGeometry

@[expose] public section
/-! An arbitrary earlier event, colour degrees, zero retention and the
constructed corrected absorber all use one expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryExpandedColourDegreeEvent
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (p k p₂ k₂ u:ℝ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):Prop :=
    ∀a x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) a x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ)

def OrdinaryColourZeroCorrectionShape
    (r d:ℕ) (hr:3≤r) (hd:2≤d) (α pstar ω L:ℝ)
    (hα:0<α) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω) (hL:0≤L):Prop :=
  ∃δ h εabs εv:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
  ∀ξ:ℝ,∀hξ:0<ξ,∀hξh:ξ≤h/100,
  ∀m:ℕ,∃a b:ℕ,∀t f q₀:ℕ,∀χcol:ℝ,0<χcol→∃N:ℕ,1≤N ∧
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
  ∀(g₀:Γ),(∀w,q w g₀=0)→
  ∀(A Z Wterm W:Finset V) (Bterm B:Finset U),
    A=Finset.univ\Z→(Z.card:ℝ)≤εabs*Fintype.card V→
    Wterm.card+Bterm.card≤t→Wterm⊆W→Bterm⊆B→W.card≤f→
    (B.card:ℝ)≤εabs*Fintype.card V+f→
    (Z.card:ℝ)≤εv*Fintype.card V→(B.card:ℝ)≤εv*Fintype.card V+f→
  ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (E:(Σσ,R σ)→Prop) (lossE:ℝ),
  let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
  let νcoin:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
  1-lossE≤(μ.sigma ν).probability E→
  1-(lossE+χcol)-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)≤
    ((μ.sigma ν).prod νcoin).probability (fun z=>
      ((E z.1 ∧ OrdinaryExpandedColourDegreeEvent P p k p₂ k₂ u z.1.1) ∧
        OrdinaryZeroRetentionEvent π d g₀ z.1.1) ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B)
end Oberwolfach
