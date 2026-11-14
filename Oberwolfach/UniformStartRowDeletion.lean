module

public import Oberwolfach.UniformStartDeletionBounds

@[expose] public section

/-! Conditional independence is across starts, not across hubs in the
same fixed-size subset. This gives the row deletion tail. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem startRemovedHubs_one_probability_le (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card)
    (a : V) (u : U) :
    (startRetentionLaw A t ht).probability (fun J=>u∈startRemovedHubs A t J a)≤
      (((A a).card-t:ℕ):ℝ)/(A a).card := by
  have hh := startRemovedHubs_joint_probability_le A t ht a {u}
  simpa only [Finset.singleton_subset_iff,Finset.card_singleton,pow_one] using hh

theorem startRemovedHubs_row_joint (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card)
    (u : U) (S : Finset V) :
    (startRetentionLaw A t ht).probability (fun J=>∀ a∈S,u∈startRemovedHubs A t J a)=
      ∏ a∈S,(startRetentionLaw A t ht).probability (fun J=>u∈startRemovedHubs A t J a) := by
  unfold startRetentionLaw
  apply finiteLaw_disjoint_supported_family _ (fun a=>{a})
  · intro a J K h
    have he := h a (Finset.mem_singleton_self a)
    unfold startRemovedHubs startRetainedHubs
    rw [he]
  · intro a _ b _ hab
    exact Finset.disjoint_singleton.mpr hab

theorem startRemovedHubs_row_joint_le (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card)
    (u : U) (S : Finset V) (p : ℝ) (hp : 0≤p)
    (hrate : ∀ a∈S,(((A a).card-t:ℕ):ℝ)/(A a).card≤p) :
    (startRetentionLaw A t ht).probability (fun J=>∀ a∈S,u∈startRemovedHubs A t J a)≤p^S.card := by
  rw [startRemovedHubs_row_joint]
  calc
    _ ≤ ∏ _a∈S,p := Finset.prod_le_prod₀ (fun _ _=>finiteLaw_probability_nonneg _ _)
      (fun a ha=>(startRemovedHubs_one_probability_le A t ht a u).trans (hrate a ha))
    _ = _ := by simp

theorem startRemovedHubs_row_tail (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card)
    (u : U) (S : Finset V) (k : ℕ) (p : ℝ) (hp : 0≤p)
    (hrate : ∀ a∈S,(((A a).card-t:ℕ):ℝ)/(A a).card≤p) :
    (startRetentionLaw A t ht).probability
      (fun J=>k≤(S.filter (fun a=>u∈startRemovedHubs A t J a)).card)≤(S.card.choose k:ℝ)*p^k := by
  let X := fun J : StartRetentionOutcome A t=>Finset.univ.filter (fun a=>u∈startRemovedHubs A t J a)
  have hh := finiteLaw_set_count_tail (startRetentionLaw A t ht) X S k p (by
    intro B hB
    obtain ⟨hBS,hcard⟩ := Finset.mem_powersetCard.mp hB
    have hb := startRemovedHubs_row_joint_le A t ht u B p hp (fun a ha=>hrate a (hBS ha))
    simpa only [X,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and,hcard] using hb)
  have he : ∀ J,S∩X J=S.filter (fun a=>u∈startRemovedHubs A t J a) := by intro J;ext a;simp [X]
  simpa only [he] using hh

end Oberwolfach
