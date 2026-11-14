module

public import Oberwolfach.FiniteLawSigmaProjection
public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.RawUniformRetentionRealExponents
public import Oberwolfach.RetainedIntervalIdentities

@[expose] public section

/-! The marked experiment keeps all raw physical and interval variables,
then retains a uniform common number of starts of one selected colour.
The projection to interval variables has exactly the previously checked
retention law, and every common raw event keeps its original probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

abbrev RawMarkedRetainedOutcome (π : Equiv.Perm V) (d : ℕ) (g : Γ) :=
  Σ σ : RawMarkedOutcome V U Γ Color,
    StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g))

def rawMarkedRetentionInterval (π : Equiv.Perm V) (d : ℕ) (g : Γ)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g) :
    RawRetainedIntervalOutcome (U:=U) (Color:=Color) π d g :=
  ⟨fun e=>z.1 (Sum.inr e),z.2⟩

def rawMarkedRetentionLaw (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d) (g : Γ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) :
    FiniteLaw (RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g) :=
  (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).sigma
    (fun σ=>startRetentionLaw (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) g))
      (startRetentionMinimum_le _))

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d) (g : Γ)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))

theorem rawMarkedRetentionLaw_interval_projection
    (E : RawRetainedIntervalOutcome (U:=U) (Color:=Color) π d g→Prop) :
    (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>E (rawMarkedRetentionInterval π d g z))=
      (rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability E := by
  unfold rawMarkedRetentionLaw rawUniformRetentionLaw rawMarkedRetentionInterval
  exact finiteLaw_pi_sigma_injective_projection
    (State:=RawMarkedCoordinateState Γ Color)
    (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)
    (Sum.inr : (U×RawIntervalCoordinate V)→RawWheelCoordinate V U) Sum.inr_injective
    (fun σ=>startRetentionLaw (rawStartHubSet π d σ g)
      (startRetentionMinimum (rawStartHubSet π d σ g)) (startRetentionMinimum_le _)) E

theorem rawMarkedRetentionLaw_raw_projection (E : RawMarkedOutcome V U Γ Color→Prop) :
    (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability (fun z=>E z.1)=
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E :=
  finiteLaw_sigma_first_probability _ _ E

theorem rawMarkedRetentionLaw_common_event
    (E : RawMarkedOutcome V U Γ Color→Prop)
    (Good : RawRetainedIntervalOutcome (U:=U) (Color:=Color) π d g→Prop) (a b : ℝ)
    (hE : 1-a≤(FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability E)
    (hG : 1-b≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability Good) :
    1-a-b≤(rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>E z.1 ∧ Good (rawMarkedRetentionInterval π d g z)) := by
  rw [← rawMarkedRetentionLaw_raw_projection π d hd g p k hp hk hphys q hq hQ s hs hS E] at hE
  rw [← rawMarkedRetentionLaw_interval_projection π d hd g p k hp hk hphys q hq hQ s hs hS Good] at hG
  exact (sub_le_sub_right hE b).trans (finiteLaw_good_intersection _ _ _ b hG)

end Oberwolfach
