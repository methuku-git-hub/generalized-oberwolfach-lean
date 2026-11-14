module

public import Oberwolfach.ExpandedZeroRetentionOnCommonEvent

@[expose] public section
/-! A compact same-sample event recording zero starts, good restriction and
empty retained indices; it can be adjoined to any prior without probability loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryZeroRetentionEvent (π:Equiv.Perm V) (d:ℕ) (g₀:Γ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):Prop :=
  let σI:=fun e=>σ (Sum.inr e)
  (∀w x,¬rawIntervalColouredStart π d (fun e=>σI (w,e)) x g₀) ∧
  ∀t (Jret:StartRetentionOutcome (rawStartHubSet π d σI g₀) t) (ζ:ℝ),0≤ζ→
    RetainedRestrictionGood π d σI g₀ t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret ∧
    (∀w,IsEmpty (retainedMarkedIndex π d σI g₀ t Jret w))

theorem ordinary_zero_retention_on_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (g₀:Γ) (hzero:∀w,q w g₀=0) (π:Equiv.Perm V)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)→Prop):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν;
    μ.probability E≤μ.probability (fun z=>E z ∧ OrdinaryZeroRetentionEvent π d g₀ z.1):=by
  intro μ
  have hh:=expanded_zero_retention_on_common_event (I:=Unit) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS g₀ hzero π ν E
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,hz.2.1,?_⟩
  intro t Jret ζ hζ
  exact hz.2.2 t Jret (fun _=>Finset.univ) (fun _=>Finset.univ) ζ hζ
end Oberwolfach
