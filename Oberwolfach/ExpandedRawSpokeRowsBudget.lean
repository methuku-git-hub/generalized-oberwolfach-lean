module

public import Oberwolfach.ExpandedRawSpokeRowsAnyStage

@[expose] public section
/-! A supplied failure budget adds the variable-density spoke rows to any
existing same-sample event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_raw_spoke_rows_with_budget
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g j:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hU:0<Fintype.card U) (t ζ:ℝ) (ht:0<t)
    (hfail:4*(Fintype.card V:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U))≤ζ)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω)):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma ν;
    ∀(E:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop)
      (ε:ℝ),1-ε≤μ.probability E→
    1-(ε+ζ)≤μ.probability (fun z=>E z ∧ ∀b v,
      |rawMarkedRestrictedSpokeRow π d (fun e=>z.1 (Sum.inr e)) g j b v Finset.univ-
        ∑u,if b then q u g else s u j|<t) :=by
  intro μ E ε hE
  have hh:=expanded_raw_spoke_row_counts_any_stage π d hd g j p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS hnoshort hU t ht ν E ε hE
  have hn:1-(ε+ζ)≤1-ε-4*(Fintype.card V:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U)):=by linarith
  exact hn.trans hh
end Oberwolfach
