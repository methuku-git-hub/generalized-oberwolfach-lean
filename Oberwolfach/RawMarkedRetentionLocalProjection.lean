module

public import Oberwolfach.RawUniformRetentionLocalEvent
public import Oberwolfach.ExpandedRetentionRestrictionProjection
public import Oberwolfach.RawMarkedRetention

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_retention_local_projection_probability
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Nonempty V]
    [LinearOrder V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g:Γ)
    (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (I:Type) (T:Finset I) (A:I→Finset V) (H:I→Finset U) (ζ:ℝ):
    (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>∀i∈T,RetainedRestrictionLocalGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) (A i) (H i) ζ z.2)=
    (rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability
      (fun z=>∀i∈T,RetainedRestrictionLocalGood π d z.1 g
        (startRetentionMinimum (rawStartHubSet π d z.1 g)) (A i) (H i) ζ z.2):=by
  let μ:=rawMarkedWheelLaw (V:=V) p k hp hk hphys d hd q hq hQ s hs hS
  let f:U×RawIntervalCoordinate V→RawWheelCoordinate V U:=Sum.inr
  let ν:=fun σ:RawIntervalFamilyOutcome V U Γ Color=>
    startRetentionLaw (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g)) (startRetentionMinimum_le _)
  let E:=fun z:RawRetainedIntervalOutcome (U:=U) (Color:=Color) π d g=>
    ∀i∈T,RetainedRestrictionLocalGood π d z.1 g (startRetentionMinimum (rawStartHubSet π d z.1 g)) (A i) (H i) ζ z.2
  have hh:=finiteLaw_pi_sigma_injective_projection μ f Sum.inr_injective ν E
  change ((FiniteLaw.pi μ).sigma (fun ω=>ν (fun e=>ω (Sum.inr e)))).probability
    (fun z=>E ⟨fun e=>z.1 (Sum.inr e),z.2⟩)=
      ((FiniteLaw.pi (fun e=>μ (Sum.inr e))).sigma ν).probability E
  exact hh
end Oberwolfach
