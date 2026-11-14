module

public import Oberwolfach.ExpandedOrientationProjection
public import Oberwolfach.CommonBalancedPositiveMass

@[expose] public section
/-! Positive mass for one original expanded outcome satisfying both the
common sampling event and the balanced-orientation event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_common_balanced_positive_mass
    (a A B:ℝ) (ha:a<1) (qexp:ℕ) (hqexp:0<qexp) (r α:ℝ) (hr:0<r) (hα:0<α):
    ∃N:ℕ,1≤N ∧ ∀
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))

    (hn:N≤Fintype.card V) (G:SimpleGraph V)
    (heven:∀v,Even (G.degree v)) (hmin:∀v,(1/2+α)*(Fintype.card V:ℝ)≤G.degree v)
    (Good:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop),
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν
    1-a-A*(Fintype.card V:ℝ)^(-(qexp:ℝ))-B*(Fintype.card V:ℝ)^(-r)≤μ.probability Good→
    ∃z,Good z ∧ BalancedSampleOrientationEvent G α (fun e=>(z.1 (Sum.inl e)).2) ∧ 0<μ.mass z:=by
  obtain ⟨N,hN,hall⟩:=common_balanced_positive_mass a A B ha qexp hqexp r hr α hα
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS R _ ν hn G heven hmin Good μ hGood
  exact hall V hn G heven hmin μ (fun z e=>(z.1 (Sum.inl e)).2)
    (fun E=>expanded_orientation_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν E) Good hGood
end Oberwolfach
