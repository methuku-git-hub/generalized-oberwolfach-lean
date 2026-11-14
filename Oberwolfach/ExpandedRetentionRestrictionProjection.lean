module

public import Oberwolfach.MixedClassActualRetention
public import Oberwolfach.FiniteLawSigmaProjection
public import Oberwolfach.RawUniformRetentionRealExponents
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! The expanded rim exposure leaves the interval law and its conditional
start retention unchanged, including every fixed restriction event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_retention_restriction_probability
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {I:Type} [Fintype I] (S:I→Finset V) (T:I→Finset U) (ζ:ℝ):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g)).probability
      (fun z=>RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) S T ζ z.2)=
    (rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability
      (fun z=>RetainedRestrictionGood π d z.1 g
        (startRetentionMinimum (rawStartHubSet π d z.1 g)) S T ζ z.2) := by
  let μ := rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS
  let f : U×RawIntervalCoordinate V → RawWheelCoordinate V U := Sum.inr
  let ν := fun σ:RawIntervalFamilyOutcome V U Bool Bool=>
    startRetentionLaw (rawStartHubSet π d σ g) (startRetentionMinimum (rawStartHubSet π d σ g)) (startRetentionMinimum_le _)
  let E := fun z:RawRetainedIntervalOutcome (U:=U) (Color:=Bool) π d g=>
    RetainedRestrictionGood π d z.1 g (startRetentionMinimum (rawStartHubSet π d z.1 g)) S T ζ z.2
  have hh:=finiteLaw_pi_sigma_injective_projection μ f Sum.inr_injective ν E
  change ((FiniteLaw.pi μ).sigma (fun ω=>ν (fun e=>ω (Sum.inr e)))).probability
    (fun z=>E ⟨fun e=>z.1 (Sum.inr e),z.2⟩)=
      ((FiniteLaw.pi (fun e=>μ (Sum.inr e))).sigma ν).probability E
  exact hh
/-- Any previously established common event can be intersected with the
retention restriction event under the same expanded-and-retained law. -/
theorem expanded_retention_restrictions_join
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {I:Type} [Fintype I] (S:I→Finset V) (T:I→Finset U) (ζ:ℝ):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g)
    ∀(E:(Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g ω)→Prop)
      (ε δ:ℝ),1-ε≤μ.probability E →
    1-δ≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability
      (fun z=>RetainedRestrictionGood π d z.1 g
        (startRetentionMinimum (rawStartHubSet π d z.1 g)) S T ζ z.2) →
    1-ε-δ≤μ.probability (fun z=>E z ∧
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) S T ζ z.2) := by
  intro μ E ε δ hE hgood
  have hp:=expanded_retention_restriction_probability π d hd g p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS S T ζ
  have hgood':1-δ≤μ.probability (fun z=>
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) S T ζ z.2) := by
    rw [hp]
    exact hgood
  exact (sub_le_sub_right hE δ).trans (finiteLaw_good_intersection μ E _ δ hgood')
/-- If the combined failure budget is below one, there is a single
positive-mass outcome satisfying both events. -/
theorem expanded_retention_restrictions_witness
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {I:Type} [Fintype I] (S:I→Finset V) (T:I→Finset U) (ζ:ℝ):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g)
    ∀(E:(Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g ω)→Prop)
      (ε δ:ℝ),1-ε≤μ.probability E →
    1-δ≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability
      (fun z=>RetainedRestrictionGood π d z.1 g
        (startRetentionMinimum (rawStartHubSet π d z.1 g)) S T ζ z.2) →
    ε+δ<1 →
    ∃z,0<μ.mass z ∧ E z ∧
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) S T ζ z.2 := by
  intro μ E ε δ hE hgood hbudget
  have hh:=expanded_retention_restrictions_join π d hd g p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS S T ζ E ε δ hE hgood
  have hpos:0<μ.probability (fun z=>E z ∧
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) S T ζ z.2) := by linarith
  exact finiteLaw_positive_event_exists μ _ hpos
end Oberwolfach
