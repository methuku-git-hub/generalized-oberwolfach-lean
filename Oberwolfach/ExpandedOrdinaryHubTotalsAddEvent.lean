module

public import Oberwolfach.OrdinaryExpandedHubTotalEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! Add all full ordinary-wheel hub-weight tests to an arbitrary event on
the same expanded sample, with an explicit additive failure cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_ordinary_hub_totals_add_to_event
    (I:Type) [Fintype I] (d:ℕ) (hd:2≤d) (m:I→ℕ) (hm:∀i,2≤m i)
    (B η:I→ℝ) (hB:∀i,0<B i) (hη:∀i,0<η i) (ζ:ℝ) (hζ:0<ζ):
    ∃N:ℕ,1≤N ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (w:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
    (hw:∀i W,0≤w i W ∧ w i W≤B i/(Fintype.card V:ℝ)^(m i)) (g:I→Γ) (j:I→Color)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (ε:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-ε≤(μ.sigma ν).probability E→
    1-(ε+ζ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryExpandedHubTotalEvent P π d m p₂ k₂ q s w g j η z.1) :=by
  obtain ⟨N,hN1,hN⟩:=expanded_ordinary_hub_total_family I d hd m hm B η hB hη ζ hζ
  refine ⟨N,hN1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j R _ ν E ε μ hE
  have htotal:=hN V U Γ Color hn hU P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j ν
  have hh:=finiteLaw_intersection_lower (μ.sigma ν) E _ ε ζ hE htotal
  simpa only [OrdinaryExpandedHubTotalEvent,sub_add_eq_sub_sub] using hh
end Oberwolfach
