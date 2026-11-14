module

public import Oberwolfach.RetainedIntervalFamily
public import Oberwolfach.UniformStartRowDeletion

@[expose] public section

/-! Conditional tails for the actual number of changed interval states.
The row proof uses independent starts; the index proof uses only the joint
exclusion bounds within each uniform retained subset. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retainedRawFamily_row_tail (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (ht : ∀ a,t≤(rawStartHubSet π d σ g₀ a).card)
    (u : U) (S : Finset V) (hS : ∀ x,π x∈S ↔ x∈S) (ζ p : ℝ) (hp : 0≤p)
    (hrate : ∀ a∈S,(((rawStartHubSet π d σ g₀ a).card-t:ℕ):ℝ)/
      (rawStartHubSet π d σ g₀ a).card≤p) :
    let k := Nat.ceil (ζ*S.card/(d+1:ℕ))
    (startRetentionLaw (rawStartHubSet π d σ g₀) t ht).probability
      (fun J=>ζ*S.card<((S.filter (fun x=>retainedRawFamilyState π d σ g₀ t J (x,u)≠
        rawIntervalFamilyState π d σ (x,u))).card:ℝ))≤(S.card.choose k:ℝ)*p^k := by
  dsimp only
  have hh := startRemovedHubs_row_tail (rawStartHubSet π d σ g₀) t ht u S
    (Nat.ceil (ζ*S.card/(d+1:ℕ))) p hp hrate
  apply le_trans _ hh
  apply finiteLaw_probability_mono
  intro J hJ
  have hg := retainedRawFamily_row_changes π d σ g₀ t J u S hS
  have hgR := Nat.cast_le (α:=ℝ).mpr hg
  rw [Nat.cast_mul] at hgR
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(d+1:ℕ))).mpr
  nlinarith only [hgR,hJ]

theorem retainedRawFamily_index_tail (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (ht : ∀ a,t≤(rawStartHubSet π d σ g₀ a).card)
    (x : V) (T : Finset U) (ζ p : ℝ) (hζ : 0≤ζ) (hp : 0≤p)
    (hrate : ∀ a∈permutationWindow π d 0 x,(((rawStartHubSet π d σ g₀ a).card-t:ℕ):ℝ)/
      (rawStartHubSet π d σ g₀ a).card≤p) :
    let k := Nat.ceil (ζ*T.card/(d+1:ℕ))
    (startRetentionLaw (rawStartHubSet π d σ g₀) t ht).probability
      (fun J=>ζ*T.card<((T.filter (fun u=>retainedRawFamilyState π d σ g₀ t J (x,u)≠
        rawIntervalFamilyState π d σ (x,u))).card:ℝ))≤(d+1:ℕ)*(T.card.choose k:ℝ)*p^k := by
  let k := Nat.ceil (ζ*T.card/(d+1:ℕ))
  let A := rawStartHubSet π d σ g₀
  let μ := startRetentionLaw A t ht
  let W := permutationWindow π d 0 x
  let E := fun a (J : StartRetentionOutcome A t)=>k≤(T∩startRemovedHubs A t J a).card
  have hsub : ∀ J,ζ*T.card<((T.filter (fun u=>retainedRawFamilyState π d σ g₀ t J (x,u)≠
        rawIntervalFamilyState π d σ (x,u))).card:ℝ) → ∃ a∈W,E a J := by
    intro J hJ
    by_contra hn
    have ha : ∀ a∈W,((T∩startRemovedHubs A t J a).card:ℝ)≤ζ*T.card/(d+1:ℕ) := by
      intro a ha
      have hk : (T∩startRemovedHubs A t J a).card<k := by
        by_contra h;exact hn ⟨a,ha,not_lt.mp h⟩
      exact (Nat.lt_ceil.mp hk).le
    have hg := retainedRawFamily_index_changes π d σ g₀ t J x T
    have hgR := Nat.cast_le (α:=ℝ).mpr hg
    rw [Nat.cast_sum] at hgR
    have hsum : (∑ a∈W,((T∩startRemovedHubs A t J a).card:ℝ))≤ζ*T.card := by
      calc
        _ ≤ ∑ _a∈W,ζ*T.card/(d+1:ℕ) := Finset.sum_le_sum ha
        _ = (W.card:ℝ)*(ζ*T.card/(d+1:ℕ)) := by simp
        _ ≤ (d+1:ℕ)*(ζ*T.card/(d+1:ℕ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast (show W.card≤d+1 by simpa [W] using permutationWindow_card_le π d 0 x)
        _ = _ := by field_simp
    exact (not_lt_of_ge (hgR.trans hsum)) hJ
  have htail (a : V) (ha : a∈W) : μ.probability (E a)≤(T.card.choose k:ℝ)*p^k := by
    have hh := startRemovedHubs_intersection_tail A t ht a T k
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hrate a ha) k) (by positivity))
  calc
    _ ≤ μ.probability (fun J=>∃ a∈W,E a J) := finiteLaw_probability_mono μ _ _ hsub
    _ ≤ ∑ a∈W,μ.probability (E a) := finiteLaw_union_bound μ W E
    _ ≤ ∑ _a∈W,(T.card.choose k:ℝ)*p^k := Finset.sum_le_sum htail
    _ = (W.card:ℝ)*((T.card.choose k:ℝ)*p^k) := by simp
    _ ≤ (d+1:ℕ)*((T.card.choose k:ℝ)*p^k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show W.card≤d+1 by simpa [W] using permutationWindow_card_le π d 0 x)
    _ = _ := by ring

end Oberwolfach
