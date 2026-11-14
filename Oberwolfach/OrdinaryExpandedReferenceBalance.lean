module

public import Oberwolfach.OrdinaryRawReferenceBalanceEvent
public import Oberwolfach.OrdinaryExpandedGeneralReferenceEvent

@[expose] public section
/-! Reference balance and an arbitrary dependent prior event hold on the same
    expanded ordinary sample, with the original factor-dependent marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_expanded_reference_balance_and_prior_event
    (P F:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (pH tR tH L:ℝ) (htR:0≤tR) (htH:0<tH) (hU:0<Fintype.card U)
    (j:Color) (hj:∀w,s w j=pH)
    (hcentre:∀v,(2*p)*(P.degree v:ℝ)=2*(pH*Fintype.card U)) (hF:∀v,(F.degree v:ℝ)≤L)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ)
    (hE:let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
      1-εE≤(μ.sigma ν).probability E):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let loss:=2*(Fintype.card V:ℝ)*Real.exp (-2*tR^2/Fintype.card V)+
      (Fintype.card V:ℝ)*(2*Real.exp (-2*tH^2/((4*(d:ℝ)+3)^2*Fintype.card U)));
    1-(εE+loss)≤(μ.sigma ν).probability (fun z=>E z ∧
      ∀v,|(((rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)))\F).degree v:ℝ)-
        2*((Finset.univ.filter (fun w=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) j v w)).card:ℝ)|≤tR+2*tH+L):=by
  intro μ loss
  have hpR:0≤2*p:=by positivity
  have hpR1:2*p≤1:=by linarith
  have hBal:=ordinary_raw_reference_balance_high_probability P F π (2*p) pH tR tH L hpR hpR1 htR htH hU
    d hd q hq hQ s hs hS hnoshort j hj hcentre hF
  exact ordinary_expanded_add_general_reference_event p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν
    (fun σ=>∀v,|(((rawWheelGraph P σ)\F).degree v:ℝ)-
      2*((Finset.univ.filter (fun w=>rawWheelSpokes π d σ j v w)).card:ℝ)|≤tR+2*tH+L)
    E loss εE hBal hE
end Oberwolfach
