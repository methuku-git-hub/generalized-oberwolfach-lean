module

public import Oberwolfach.UniformStartRetention

@[expose] public section

/-! Conditional deletion probabilities for a fixed start. No independent
hub deletions are substituted for the uniform retained subset. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem startRemovedHubs_subset_iff (A : V→Finset U) (t : ℕ) (J : StartRetentionOutcome A t)
    (a : V) (T : Finset U) (hT : T⊆A a) :
    T⊆startRemovedHubs A t J a ↔ T.subtype (fun u=>u∈A a)⊆(J a).valᶜ := by
  constructor
  · intro h v hv
    have hvT : v.val∈T := by simpa using hv
    have hd := h hvT
    obtain ⟨_,hn⟩ := Finset.mem_sdiff.mp hd
    apply Finset.mem_compl.mpr
    intro hj
    exact hn (Finset.mem_map.mpr ⟨v,hj,rfl⟩)
  · intro h u hu
    have huA := hT hu
    have hn := h (show (⟨u,huA⟩ : {u // u∈A a})∈T.subtype (fun u=>u∈A a) by simpa using hu)
    apply Finset.mem_sdiff.mpr
    refine ⟨huA,?_⟩
    intro hj
    obtain ⟨v,hv,he⟩ := Finset.mem_map.mp hj
    apply Finset.mem_compl.mp hn
    have he' : v=(⟨u,huA⟩ : {u // u∈A a}) := Subtype.ext he
    exact he' ▸ hv

theorem startRemovedHubs_joint_probability_le (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card)
    (a : V) (T : Finset U) :
    (startRetentionLaw A t ht).probability (fun J=>T⊆startRemovedHubs A t J a)≤
      (((A a).card-t:ℕ):ℝ)^T.card/((A a).card:ℝ)^T.card := by
  by_cases hT : T⊆A a
  · letI : Nonempty (FixedSubset {u // u∈A a} t) := fixedSubset_nonempty (by simpa using ht a)
    simp_rw [startRemovedHubs_subset_iff A t _ a T hT]
    rw [startRetentionLaw_coordinate_event A t ht a
      (fun X=>T.subtype (fun u=>u∈A a)⊆X.valᶜ)]
    have hh := fixedSubset_joint_exclusion_le (V:={u // u∈A a}) (by simpa using ht a)
      (T.subtype (fun u=>u∈A a))
    have hc : (T.subtype (fun u=>u∈A a)).card=T.card := by
      rw [Finset.card_subtype]
      rw [Finset.filter_eq_self.mpr (fun u hu=>hT hu)]
    simp only [Finset.subset_iff,Finset.mem_compl] at hh ⊢
    simpa only [hc,Fintype.card_coe] using hh
  · have he : (fun J : StartRetentionOutcome A t=>T⊆startRemovedHubs A t J a)=(fun _=>False) := by
      funext J
      apply propext
      constructor
      · intro h;exact hT (h.trans Finset.sdiff_subset)
      · exact False.elim
    rw [he]
    simp only [FiniteLaw.probability,ite_false,Finset.sum_const_zero]
    positivity

theorem startRemovedHubs_intersection_tail (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card)
    (a : V) (T : Finset U) (k : ℕ) :
    (startRetentionLaw A t ht).probability (fun J=>k≤(T∩startRemovedHubs A t J a).card)≤
      (T.card.choose k:ℝ)*((((A a).card-t:ℕ):ℝ)/(A a).card)^k := by
  apply finiteLaw_set_count_tail (startRetentionLaw A t ht) (fun J=>startRemovedHubs A t J a) T k _
  intro S hS
  have hc := (Finset.mem_powersetCard.mp hS).2
  have hh := startRemovedHubs_joint_probability_le A t ht a S
  simpa only [hc,div_pow] using hh

end Oberwolfach
