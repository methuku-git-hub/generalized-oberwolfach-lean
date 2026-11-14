module

public import Oberwolfach.RetentionConditionalTails
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! All fixed row and index restrictions are tested on one conditional
retention sample. No independence between tests is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color I : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
  [DecidableEq V] [DecidableEq U]

def RetainedRestrictionGood (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (S : I→Finset V) (T : I→Finset U) (ζ : ℝ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) : Prop :=
  ∀ i, (∀ u,(( (S i).filter (fun x=>retainedRawFamilyState π d σ g₀ t J (x,u)≠
    rawIntervalFamilyState π d σ (x,u))).card:ℝ)≤ζ*(S i).card) ∧
    (∀ x,(((T i).filter (fun u=>retainedRawFamilyState π d σ g₀ t J (x,u)≠
    rawIntervalFamilyState π d σ (x,u))).card:ℝ)≤ζ*(T i).card)

theorem retainedRestriction_common_event (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (ht : ∀ a,t≤(rawStartHubSet π d σ g₀ a).card)
    (S : I→Finset V) (T : I→Finset U) (hS : ∀ i x,π x∈S i ↔ x∈S i)
    (ζ p F : ℝ) (hζ : 0≤ζ) (hp : 0≤p)
    (hrate : ∀ a,(((rawStartHubSet π d σ g₀ a).card-t:ℕ):ℝ)/(rawStartHubSet π d σ g₀ a).card≤p)
    (hrow : ∀ i,((S i).card.choose (Nat.ceil (ζ*(S i).card/(d+1:ℕ))):ℝ)*
      p^(Nat.ceil (ζ*(S i).card/(d+1:ℕ)))≤F)
    (hcol : ∀ i,((T i).card.choose (Nat.ceil (ζ*(T i).card/(d+1:ℕ))):ℝ)*
      p^(Nat.ceil (ζ*(T i).card/(d+1:ℕ)))≤F) :
    1-(Fintype.card I:ℝ)*(Fintype.card U+(d+1:ℕ)*Fintype.card V)*F≤
    (startRetentionLaw (rawStartHubSet π d σ g₀) t ht).probability
      (RetainedRestrictionGood π d σ g₀ t S T ζ) := by
  let μ := startRetentionLaw (rawStartHubSet π d σ g₀) t ht
  let ER := fun (i : I×U) (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t)=>
    ζ*(S i.1).card<(((S i.1).filter (fun x=>retainedRawFamilyState π d σ g₀ t J (x,i.2)≠
      rawIntervalFamilyState π d σ (x,i.2))).card:ℝ)
  let EC := fun (i : I×V) (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t)=>
    ζ*(T i.1).card<(((T i.1).filter (fun u=>retainedRawFamilyState π d σ g₀ t J (i.2,u)≠
      rawIntervalFamilyState π d σ (i.2,u))).card:ℝ)
  have hr (i : I×U) : μ.probability (ER i)≤F :=
    (retainedRawFamily_row_tail π d σ g₀ t ht i.2 (S i.1) (hS i.1) ζ p hp (fun a _=>hrate a)).trans (hrow i.1)
  have hc (i : I×V) : μ.probability (EC i)≤(d+1:ℕ)*F := by
    have hh := retainedRawFamily_index_tail π d σ g₀ t ht i.2 (T i.1) ζ p hζ hp (fun a _=>hrate a)
    exact hh.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcol i.1) (by positivity : (0:ℝ)≤(d+1:ℕ)))
  have hR := finiteLaw_common_event_lower μ (Finset.univ : Finset (I×U)) ER (fun _=>F) (fun i _=>hr i)
  have hC := finiteLaw_common_event_lower μ (Finset.univ : Finset (I×V)) EC (fun _=>(d+1:ℕ)*F) (fun i _=>hc i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,nsmul_eq_mul,Nat.cast_mul,
    Finset.mem_univ,true_implies] at hR hC
  have hj := finiteLaw_good_intersection μ (fun J=>∀ i : I×U,¬ER i J) (fun J=>∀ i : I×V,¬EC i J)
    ((Fintype.card I:ℝ)*Fintype.card V*((d+1:ℕ)*F)) hC
  have hb := (sub_le_sub_right hR _).trans hj
  have he : 1-(Fintype.card I:ℝ)*Fintype.card U*F-
      (Fintype.card I:ℝ)*Fintype.card V*((d+1:ℕ)*F)=
      1-(Fintype.card I:ℝ)*(Fintype.card U+(d+1:ℕ)*Fintype.card V)*F := by ring
  rw [he] at hb
  apply hb.trans
  apply finiteLaw_probability_mono
  intro J hJ i
  exact ⟨fun u=>not_lt.mp (hJ.1 (i,u)),fun x=>not_lt.mp (hJ.2 (i,x))⟩

end Oberwolfach
