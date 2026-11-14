module

public import Oberwolfach.RetentionRestrictionCommonEvent

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def RetainedRestrictionLocalGood {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (A:Finset V) (H:Finset U) (ζ:ℝ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t):Prop :=
  (∀w∈H,(((A.filter (fun x=>retainedRawFamilyState π d σ g₀ t J (x,w)≠
      rawIntervalFamilyState π d σ (x,w))).card:ℝ)≤ζ*A.card)) ∧
  (∀x∈A,(((H.filter (fun w=>retainedRawFamilyState π d σ g₀ t J (x,w)≠
      rawIntervalFamilyState π d σ (x,w))).card:ℝ)≤ζ*H.card))

theorem retained_restriction_local_event
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀:Γ) (t:ℕ)
    (ht:∀a,t≤(rawStartHubSet π d σ g₀ a).card)
    (A:Finset V) (H:Finset U) (hA:∀x,π x∈A↔x∈A)
    (ζ p Fr Fc:ℝ) (hζ:0≤ζ) (hp:0≤p)
    (hrate:∀a,(((rawStartHubSet π d σ g₀ a).card-t:ℕ):ℝ)/(rawStartHubSet π d σ g₀ a).card≤p)
    (hrow:((A.card.choose (Nat.ceil (ζ*A.card/(d+1:ℕ)))):ℝ)*p^(Nat.ceil (ζ*A.card/(d+1:ℕ)))≤Fr)
    (hcol:((H.card.choose (Nat.ceil (ζ*H.card/(d+1:ℕ)))):ℝ)*p^(Nat.ceil (ζ*H.card/(d+1:ℕ)))≤Fc):
    let μ:=startRetentionLaw (rawStartHubSet π d σ g₀) t ht
    1-(H.card:ℝ)*Fr-(A.card:ℝ)*((d+1:ℕ)*Fc) ≤ μ.probability (RetainedRestrictionLocalGood π d σ g₀ t A H ζ):=by
  intro μ
  let ER:=fun w (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)=>
    ζ*A.card<(((A.filter (fun x=>retainedRawFamilyState π d σ g₀ t J (x,w)≠rawIntervalFamilyState π d σ (x,w))).card:ℝ))
  let EC:=fun x (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)=>
    ζ*H.card<(((H.filter (fun w=>retainedRawFamilyState π d σ g₀ t J (x,w)≠rawIntervalFamilyState π d σ (x,w))).card:ℝ))
  have hr:∀w∈H,μ.probability (ER w)≤Fr:=by
    intro w hw
    exact (retainedRawFamily_row_tail π d σ g₀ t ht w A hA ζ p hp (fun a _=>hrate a)).trans hrow
  have hc:∀x∈A,μ.probability (EC x)≤(d+1:ℕ)*Fc:=by
    intro x hx
    have hh:=retainedRawFamily_index_tail π d σ g₀ t ht x H ζ p hζ hp (fun a _=>hrate a)
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcol (by positivity : (0:ℝ)≤(d+1:ℕ)))
  have hR:=finiteLaw_common_event_lower μ H ER (fun _=>Fr) hr
  have hC:=finiteLaw_common_event_lower μ A EC (fun _=>(d+1:ℕ)*Fc) hc
  simp only [Finset.sum_const,nsmul_eq_mul] at hR hC
  have hi:=finiteLaw_good_intersection μ (fun J=>∀w∈H,¬ER w J) (fun J=>∀x∈A,¬EC x J)
    ((A.card:ℝ)*((d+1:ℕ)*Fc)) hC
  have hh:1-(H.card:ℝ)*Fr-(A.card:ℝ)*((d+1:ℕ)*Fc) ≤
      μ.probability (fun J=>(∀w∈H,¬ER w J) ∧ (∀x∈A,¬EC x J)):= (sub_le_sub_right hR _).trans hi
  refine hh.trans ?_
  apply finiteLaw_probability_mono
  intro J hJ
  constructor
  · intro w hw
    exact not_lt.mp (hJ.1 w hw)
  · intro x hx
    exact not_lt.mp (hJ.2 x hx)
end Oberwolfach
