module

public import Oberwolfach.ExpandedOrientationProjection
public import Oberwolfach.CommonBalancedOrientationEvent

@[expose] public section
/-! Add balanced orientation to the existing event on the very same expanded
sample, including its dependent retention coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_common_balanced_orientation
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))

    (α:ℝ) (hα:0<α) (qexp:ℕ) (G:SimpleGraph V)
    (hN:Classical.choose (balancedOrientation_highProbability_pow.{0} hα qexp)≤Fintype.card V)
    (heven:∀v,Even (G.degree v))
    (hmin:∀v,(1/2+α)*(Fintype.card V:ℝ)≤G.degree v)
    (Good:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop)
    (ε:ℝ)
    (hGood:1-ε≤((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability Good):
    1-ε-1/(Fintype.card V:ℝ)^qexp≤
      ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
        (fun z=>Good z ∧ BalancedSampleOrientationEvent G α (fun e=>(z.1 (Sum.inl e)).2)):=by
  apply finiteLaw_common_balanced_orientation _ (fun z e=>(z.1 (Sum.inl e)).2) ?_ α hα qexp G hN heven hmin Good ε hGood
  intro E
  exact expanded_orientation_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν E
end Oberwolfach
