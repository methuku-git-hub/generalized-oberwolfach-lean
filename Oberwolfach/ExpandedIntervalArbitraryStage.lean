module

public import Oberwolfach.ExpandedRetainedHubEvent

@[expose] public section
/-! The interval marginal is unchanged by an arbitrary second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_interval_event_probability_arbitrary_stage
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (d:ℕ) (hd:2≤d) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (E:RawIntervalFamilyOutcome V U Γ Color→Prop):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν).probability
      (fun z=>E (fun e=>z.1 (Sum.inr e)))=
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E :=by
  let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
  let E':(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Prop:=fun σ=>E (fun e=>σ (Sum.inr e))
  calc
    _ = μ.probability E' :=finiteLaw_sigma_first_probability μ ν E'
    _ = _ :=by
      exact finiteLaw_pi_injective_projection_event
        (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
        Sum.inr Sum.inr_injective E
end Oberwolfach
