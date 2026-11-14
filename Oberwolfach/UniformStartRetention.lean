module

public import Oberwolfach.AmbientSubset
public import Oberwolfach.SubsetDeletionTails
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! The conditional retention law: at each start choose a uniform t-subset
of its actual eligible hubs, independently across starts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

abbrev StartRetentionOutcome (A : V→Finset U) (t : ℕ) := ∀ a,FixedSubset {u // u∈A a} t

def startRetentionLaw (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card) :
    FiniteLaw (StartRetentionOutcome A t) :=
  FiniteLaw.pi (fun a=>by
    letI : Nonempty (FixedSubset {u // u∈A a} t) := fixedSubset_nonempty (by simpa using ht a)
    exact FiniteLaw.uniform (FixedSubset {u // u∈A a} t))

def startRetainedHubs (A : V→Finset U) (t : ℕ) (J : StartRetentionOutcome A t) (a : V) : Finset U :=
  (J a).val.map (Function.Embedding.subtype _)

def startRemovedHubs (A : V→Finset U) (t : ℕ) (J : StartRetentionOutcome A t) (a : V) : Finset U :=
  A a\startRetainedHubs A t J a

theorem startRetainedHubs_subset (A : V→Finset U) (t : ℕ) (J : StartRetentionOutcome A t) (a : V) :
    startRetainedHubs A t J a⊆A a := subtype_sample_subset (A a) (J a).val

theorem startRetainedHubs_card (A : V→Finset U) (t : ℕ) (J : StartRetentionOutcome A t) (a : V) :
    (startRetainedHubs A t J a).card=t := by
  rw [startRetainedHubs,Finset.card_map]
  exact (J a).property

theorem startRemovedHubs_card (A : V→Finset U) (t : ℕ) (J : StartRetentionOutcome A t) (a : V) :
    (startRemovedHubs A t J a).card=(A a).card-t := by
  rw [startRemovedHubs,Finset.card_sdiff_of_subset (startRetainedHubs_subset A t J a),startRetainedHubs_card]

theorem startRetentionLaw_coordinate_event (A : V→Finset U) (t : ℕ) (ht : ∀ a,t≤(A a).card)
    (a : V) (E : FixedSubset {u // u∈A a} t→Prop) :
    letI : Nonempty (FixedSubset {u // u∈A a} t) := fixedSubset_nonempty (by simpa using ht a)
    (startRetentionLaw A t ht).probability (fun J=>E (J a))=
      (FiniteLaw.uniform (FixedSubset {u // u∈A a} t)).probability E := by
  unfold startRetentionLaw
  exact finiteLaw_pi_coordinate_event (State:=fun a=>FixedSubset {u // u∈A a} t) _ a E

theorem startRemovedHubs_complement (A : V→Finset U) (t : ℕ) (J : StartRetentionOutcome A t) (a : V) :
    startRemovedHubs A t J a=((J a).valᶜ).map (Function.Embedding.subtype _) := by
  ext u
  simp only [startRemovedHubs,startRetainedHubs,Finset.mem_sdiff,Finset.mem_map,Function.Embedding.subtype_apply,
    Finset.mem_compl]
  constructor
  · rintro ⟨hu,hnot⟩
    refine ⟨⟨u,hu⟩,?_,rfl⟩
    intro hmem
    exact hnot ⟨⟨u,hu⟩,hmem,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    refine ⟨v.property,?_⟩
    rintro ⟨w,hw,he⟩
    exact hv ((Subtype.ext he) ▸ hw)

end Oberwolfach
