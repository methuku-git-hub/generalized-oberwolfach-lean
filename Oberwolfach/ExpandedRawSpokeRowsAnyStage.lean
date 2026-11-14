module

public import Oberwolfach.RawVariableSpokeRowCounts
public import Oberwolfach.ExpandedRetainedHubEvent

@[expose] public section
/-! Add the variable-density raw spoke-row event to any existing event on
the same expanded sample, including any dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_raw_spoke_row_counts_any_stage
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g j:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hU:0<Fintype.card U) (t:ℝ) (ht:0<t)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω)):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma ν
    let failure:=4*(Fintype.card V:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U));
    ∀(E:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop)
      (ε:ℝ),1-ε≤μ.probability E→
    1-ε-failure≤μ.probability (fun z=>E z ∧ ∀b v,
      |rawMarkedRestrictedSpokeRow π d (fun e=>z.1 (Sum.inr e)) g j b v Finset.univ-
        ∑u,if b then q u g else s u j|<t) :=by
  intro μ failure E ε hE
  have hraw:=raw_variable_spoke_row_counts_event π d hd q hq hQ s hs hS hnoshort hU g j t ht
  let E':(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)→Prop:=
    fun ω=>∀b v,|rawMarkedRestrictedSpokeRow π d (fun e=>ω (Sum.inr e)) g j b v Finset.univ-
      ∑u,if b then q u g else s u j|<t
  have hprojection:μ.probability (fun z=>E' z.1)=
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀b v,|rawMarkedRestrictedSpokeRow π d σ g j b v Finset.univ-
          ∑u,if b then q u g else s u j|<t):=by
    calc
      _ = (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).probability E' :=
        finiteLaw_sigma_first_probability _ ν E'
      _ = _ :=by
        let h:U×RawIntervalCoordinate V→RawWheelCoordinate V U:=Sum.inr
        exact finiteLaw_pi_injective_projection_event
          (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)
          h Sum.inr_injective (fun σ=>∀b v,|rawMarkedRestrictedSpokeRow π d σ g j b v Finset.univ-
            ∑u,if b then q u g else s u j|<t)
  have hraw':1-failure≤μ.probability (fun z=>E' z.1):=by rw [hprojection];exact hraw
  exact (sub_le_sub_right hE failure).trans (finiteLaw_good_intersection μ E _ failure hraw')
end Oberwolfach
