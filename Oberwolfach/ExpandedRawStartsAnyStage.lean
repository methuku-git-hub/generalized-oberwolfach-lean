module

public import Oberwolfach.RawIntervalHubStartEvent
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! Add the simultaneous interval-start counts to any event on the same
expanded sample and any subsequent finite dependent exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_raw_starts_any_stage
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t:ℝ) (ht:0<t)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)→Type} [∀ω,Fintype (R ω)]
    (ν:∀ω,FiniteLaw (R ω)):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma ν
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V))
    ∀(E:(Σ ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop)
      (ε:ℝ),1-ε≤μ.probability E →
    1-ε-failure≤μ.probability (fun z=>E z ∧ ∀u g,
      |rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<t) :=by
  intro μ failure E ε hE
  have hraw:=rawIntervalHubStartCount_all_event π d hd q hq hQ s hs hS Fintype.card_pos hnoshort t ht
  have hprojection:μ.probability (fun z=>∀u g,
      |rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<t)=
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀u g,|rawIntervalHubStartCount π d g σ u-(Fintype.card V:ℝ)*q u g/d|<t):=by
    let E' : (∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)→Prop :=
      fun ω=>∀u g,|rawIntervalHubStartCount π d g (fun e=>ω (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<t
    calc
      _ = (FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).probability E' :=
        finiteLaw_sigma_first_probability _ ν E'
      _ = _ := by
        let h : U×RawIntervalCoordinate V → RawWheelCoordinate V U := Sum.inr
        have hh:=finiteLaw_pi_injective_projection_event
          (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)
          h Sum.inr_injective (fun σ=>∀u g,|rawIntervalHubStartCount π d g σ u-(Fintype.card V:ℝ)*q u g/d|<t)
        exact hh
  have hraw':1-failure≤μ.probability (fun z=>∀u g,
      |rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<t):=by
    rw [hprojection]
    convert hraw using 1 <;> simp only [failure,Fintype.card_bool,Nat.cast_ofNat] <;> ring
  exact (sub_le_sub_right hE failure).trans (finiteLaw_good_intersection μ E _ failure hraw')
end Oberwolfach
