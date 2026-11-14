module

public import Oberwolfach.RetentionRestrictionLocalEvent
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_restriction_local_family
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (ht:∀a,t≤(rawStartHubSet π d σ g₀ a).card)
    (I:Type) (T:Finset I) (A:I→Finset V) (H:I→Finset U) (hA:∀i∈T,∀x,π x∈A i↔x∈A i)
    (ζ p:ℝ) (Fr Fc:I→ℝ) (hζ:0≤ζ) (hp:0≤p)
    (hrate:∀a,(((rawStartHubSet π d σ g₀ a).card-t:ℕ):ℝ)/(rawStartHubSet π d σ g₀ a).card≤p)
    (hrow:∀i∈T,((A i).card.choose (Nat.ceil (ζ*(A i).card/(d+1:ℕ))):ℝ)*p^(Nat.ceil (ζ*(A i).card/(d+1:ℕ)))≤Fr i)
    (hcol:∀i∈T,((H i).card.choose (Nat.ceil (ζ*(H i).card/(d+1:ℕ))):ℝ)*p^(Nat.ceil (ζ*(H i).card/(d+1:ℕ)))≤Fc i):
    let μ:=startRetentionLaw (rawStartHubSet π d σ g₀) t ht
    1-(∑i∈T,(((H i).card:ℝ)*Fr i+((A i).card:ℝ)*((d+1:ℕ)*Fc i))) ≤
      μ.probability (fun J=>∀i∈T,RetainedRestrictionLocalGood π d σ g₀ t (A i) (H i) ζ J):=by
  intro μ
  let E:=fun i=>RetainedRestrictionLocalGood π d σ g₀ t (A i) (H i) ζ
  have hEach:∀i∈T,1-(((H i).card:ℝ)*Fr i+((A i).card:ℝ)*((d+1:ℕ)*Fc i))≤μ.probability (E i):=by
    intro i hi
    have hh:=retained_restriction_local_event π d σ g₀ t ht (A i) (H i) (hA i hi) ζ p (Fr i) (Fc i) hζ hp hrate (hrow i hi) (hcol i hi)
    dsimp only at hh
    linarith only [hh]
  exact finiteLaw_high_events_common μ T E (fun i=>((H i).card:ℝ)*Fr i+((A i).card:ℝ)*((d+1:ℕ)*Fc i)) hEach
end Oberwolfach
