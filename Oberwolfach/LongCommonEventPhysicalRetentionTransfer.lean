module

public import Oberwolfach.ExpandedSamplePhysicalClassLaw
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! A deterministic continuation on the support of the same expanded sample
transfers its high-probability bound to the original physical retention law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_common_event_physical_retention_transfer
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀v g,0≤q v g) (hQ:∀v,∑g,q v g≤1/8)
    (s:U→Color→ℝ) (hs:∀v j,0≤s v j) (hS:∀v,∑j,s v j ≤ intervalUncoveredProbability d (∑g,q v g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)→Prop) (Good:SimpleGraph V→Prop) (loss χ:ℝ) (n:ℕ)
    (hbudget:loss≤χ):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)).sigma ν;
    (1-loss≤μ.probability E)→
    (∀z,0<μ.mass z→E z→Good (longPhysicalStateGraph P z.1 {0,1,2,3,4}))→
    1-χ-1/(n:ℝ)^10≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin (2*p+2*k+2*p₂+2*k₂+u)
        (by positivity) hsum)).probability (fun σ=>Good (retainedGraph P σ)) :=by
  intro μ hprob himp
  have hproject:=hprob.trans (finiteLaw_probability_mono_on_support μ E
    (fun z=>Good (longPhysicalStateGraph P z.1 {0,1,2,3,4})) himp)
  have hphysical:=expanded_sample_physical_class_probability P p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν Good
  change _≤_ at hproject
  rw [hphysical] at hproject
  have hn:0≤1/(n:ℝ)^10:=by positivity
  linarith
end Oberwolfach
