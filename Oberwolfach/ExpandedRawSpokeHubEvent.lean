module

public import Oberwolfach.ExpandedRetainedHubEvent
public import Oberwolfach.RawVariableSpokeHubCounts

@[expose] public section
/-! The approximate packing's two raw spoke types have their correct
hub-specific counts on the same expanded-and-retained common outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_raw_spoke_hub_counts_common_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (g₀ g j:Bool)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (t:ℝ) (ht:0<t):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g₀)
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V))
    ∀(E:(Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g₀ ω)→Prop)
      (ε:ℝ),1-ε≤μ.probability E →
    1-ε-failure≤μ.probability (fun z=>E z ∧ ∀b u,
      |rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) g j b u Finset.univ-
        (if b then q u g else s u j)*(Fintype.card V:ℝ)|<t) := by
  intro μ failure E ε hE
  have hraw:=raw_variable_spoke_hub_counts_event π d hd q hq hQ s hs hS hnoshort Fintype.card_pos g j t ht
  have hprojection:=expanded_interval_event_probability π d hd g₀ p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS (fun σ=>∀b u,|rawMarkedRestrictedSpokeCol π d σ g j b u Finset.univ-
      (if b then q u g else s u j)*(Fintype.card V:ℝ)|<t)
  have hraw':1-failure≤μ.probability (fun z=>∀b u,
      |rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) g j b u Finset.univ-
        (if b then q u g else s u j)*(Fintype.card V:ℝ)|<t):=by rw [hprojection];exact hraw
  exact (sub_le_sub_right hE failure).trans (finiteLaw_good_intersection μ E _ failure hraw')
end Oberwolfach
