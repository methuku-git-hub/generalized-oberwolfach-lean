module

public import Oberwolfach.ExpandedZeroMarkedStartsSupport
public import Oberwolfach.RetentionNoStartsGood
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Zero-mass marked starts and the resulting retention properties can be
added to any event on the same expanded sample without probability loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_zero_retention_on_common_event
    {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
    [LinearOrder V] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (g₀:Γ) (hzero:∀w,q w g₀=0) (π:Equiv.Perm V)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)→Prop):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν;
    μ.probability E≤μ.probability (fun z=>E z ∧
      let σI:=fun e=>z.1 (Sum.inr e);
      (∀w x,¬rawIntervalColouredStart π d (fun e=>σI (w,e)) x g₀) ∧
      ∀t (Jret:StartRetentionOutcome (rawStartHubSet π d σI g₀) t)
        (S:I→Finset V) (T:I→Finset U) (ζ:ℝ),0≤ζ→
        RetainedRestrictionGood π d σI g₀ t S T ζ Jret ∧
        (∀w,IsEmpty (retainedMarkedIndex π d σI g₀ t Jret w))):=by
  intro μ
  apply finiteLaw_probability_mono_on_support μ
  intro z hpos hE
  have hstarts:=expanded_zero_marked_starts_on_support p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS g₀ hzero ν z hpos π
  refine ⟨hE,hstarts,?_⟩
  intro t Jret S T ζ hζ
  exact retention_good_and_empty_roots_of_no_starts π d (fun e=>z.1 (Sum.inr e)) g₀ t Jret hstarts S T ζ hζ
end Oberwolfach
