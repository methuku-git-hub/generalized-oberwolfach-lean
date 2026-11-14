module

public import Oberwolfach.ExpandedRetentionRestrictionProjection
public import Oberwolfach.RawVariableHubLabelCounts

@[expose] public section
/-! The same expanded-and-retained outcome carries the earlier common
event, fixed-domain retention bounds and all variable-density hub counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_interval_event_probability
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (E:RawIntervalFamilyOutcome V U Bool Bool→Prop):
    ((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g)).probability
      (fun z=>E (fun e=>z.1 (Sum.inr e)))=
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability E := by
  let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
    p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)
  let E' : MixedClassRaw (V:=V) (U:=U) true→Prop:=fun ω=>E (fun e=>ω (Sum.inr e))
  calc
    _ = μ.probability E' := finiteLaw_sigma_first_probability μ (mixedClassActualRetention true π d g) E'
    _ = _ := by
      let f : U×RawIntervalCoordinate V → RawWheelCoordinate V U := Sum.inr
      have hh:=finiteLaw_pi_injective_projection_event
        (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)
        f Sum.inr_injective E
      exact hh

theorem expanded_retained_hub_counts_common_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g₀ j:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ζ t:ℝ) (ht:0<t):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g₀)
    let failure:=(Fintype.card U:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V))))
    ∀(E:(Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g₀ ω)→Prop)
      (ε δ:ℝ),1-ε≤μ.probability E →
    1-δ≤(rawUniformRetentionLaw π d hd g₀ q hq hQ s hs hS).probability
      (fun z=>RetainedRestrictionGood π d z.1 g₀
        (startRetentionMinimum (rawStartHubSet π d z.1 g₀))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2) →
    1-ε-δ-failure≤μ.probability (fun z=>E z ∧
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g₀
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 ∧
      ∀u,|rawIntervalNeighbourCount π d (fun e=>z.1 (Sum.inr e)) j Finset.univ {u}-
        (Fintype.card V:ℝ)*s u j|<t) := by
  intro μ failure E ε δ hE hgood
  have hjoin:=expanded_retention_restrictions_join π d hd g₀ p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ E ε δ hE hgood
  have hraw:=raw_variable_hub_label_counts_event π d hd q hq hQ s hs hS hnoshort Fintype.card_pos j t ht
  have hprojection:=expanded_interval_event_probability π d hd g₀ p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS (fun σ=>∀u,|rawIntervalNeighbourCount π d σ j Finset.univ {u}-
      (Fintype.card V:ℝ)*s u j|<t)
  have hraw':1-failure≤μ.probability (fun z=>∀u,
      |rawIntervalNeighbourCount π d (fun e=>z.1 (Sum.inr e)) j Finset.univ {u}-
        (Fintype.card V:ℝ)*s u j|<t):=by rw [hprojection];exact hraw
  have hboth:1-ε-δ-failure≤μ.probability (fun z=>(E z ∧
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g₀
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2) ∧
      ∀u,|rawIntervalNeighbourCount π d (fun e=>z.1 (Sum.inr e)) j Finset.univ {u}-
        (Fintype.card V:ℝ)*s u j|<t) :=
    (sub_le_sub_right hjoin failure).trans (finiteLaw_good_intersection μ _ _ failure hraw')
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1,hz.1.2,hz.2⟩
theorem expanded_retained_hub_counts_witness
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g₀ j:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ζ t:ℝ) (ht:0<t):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g₀)
    let failure:=(Fintype.card U:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V))))
    ∀(E:(Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g₀ ω)→Prop)
      (ε δ:ℝ),1-ε≤μ.probability E →
    1-δ≤(rawUniformRetentionLaw π d hd g₀ q hq hQ s hs hS).probability
      (fun z=>RetainedRestrictionGood π d z.1 g₀
        (startRetentionMinimum (rawStartHubSet π d z.1 g₀))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2) →
    ε+δ+failure<1 →
    ∃z,0<μ.mass z ∧ E z ∧
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g₀
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 ∧
      ∀u,|rawIntervalNeighbourCount π d (fun e=>z.1 (Sum.inr e)) j Finset.univ {u}-
        (Fintype.card V:ℝ)*s u j|<t := by
  intro μ failure E ε δ hE hgood hbudget
  have hh:=expanded_retained_hub_counts_common_event π d hd g₀ j p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS hnoshort ζ t ht E ε δ hE hgood
  have hpos:0<μ.probability (fun z=>E z ∧
      RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g₀
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 ∧
      ∀u,|rawIntervalNeighbourCount π d (fun e=>z.1 (Sum.inr e)) j Finset.univ {u}-
        (Fintype.card V:ℝ)*s u j|<t) := by linarith
  exact finiteLaw_positive_event_exists μ _ hpos
end Oberwolfach
