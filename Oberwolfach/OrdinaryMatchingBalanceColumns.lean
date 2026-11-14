module

public import Oberwolfach.OrdinaryPriorBalanceAndColumns
public import Oberwolfach.FiniteLawIntersectionLower
public import Oberwolfach.OrdinaryExpandedReferenceBalance
public import Oberwolfach.OrdinaryExpandedReferenceSpokeColumns

@[expose] public section
/-! Keep reference row balance and all spoke-column counts on any prior of
the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_with_reference_balance_and_columns
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Fbad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hn:0<n) (hU:0<Fintype.card U)
    (pH tR tH LF tS:ℝ) (htR:0≤tR) (htH:0<tH) (htS:0<tS)
    (hspoke:∀w,s w false=pH)
    (hcentre:∀v,(2*p)*(P.degree v:ℝ)=2*(pH*Fintype.card U)) (hF:∀v,(Fbad.degree v:ℝ)≤LF)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E Match:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE lossM:ℝ):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let lossB:=2*(n:ℝ)*Real.exp (-2*tR^2/n)+
      (n:ℝ)*(2*Real.exp (-2*tH^2/((4*(d:ℝ)+3)^2*Fintype.card U)))
    let lossS:=4*(Fintype.card U:ℝ)*Real.exp (-2*tS^2/((4*(d:ℝ)+3)^2*n));
    1-εE≤(μ.sigma ν).probability E→
    (∀(E':(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (ε':ℝ),
      1-ε'≤(μ.sigma ν).probability E'→1-(ε'+lossM)≤(μ.sigma ν).probability (fun z=>E' z ∧ Match z))→
    1-(((εE+lossB)+lossS)+lossM)≤(μ.sigma ν).probability (fun z=>
      ((E z ∧ (∀v,|(((rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)))\Fbad).degree v:ℝ)-
        2*((Finset.univ.filter (fun w=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)|≤tR+2*tH+LF)) ∧
      (∀w,|((Finset.univ.filter (fun v=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)-pH*n|<tS)) ∧ Match z):=by
  intro μ lossB lossS hE hMatch
  let Bal:=fun z:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)=>
    ∀v,|(((rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)))\Fbad).degree v:ℝ)-
      2*((Finset.univ.filter (fun w=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)|≤tR+2*tH+LF
  let Col:=fun z:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)=>
    ∀w,|((Finset.univ.filter (fun v=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)-pH*n|<tS
  have hb:=ordinary_prior_reference_balance_and_columns P Fbad π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    hnoshort hn hU pH tR tH LF tS htR htH htS hspoke hcentre hF ν E εE hE
  let E':(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop:=fun z=>(E z∧Bal z)∧Col z
  have hb':1-((εE+lossB)+lossS)≤(μ.sigma ν).probability E':=by
    simpa only [E',Bal,Col,lossB,lossS] using hb
  exact hMatch E' ((εE+lossB)+lossS) hb'
end Oberwolfach
