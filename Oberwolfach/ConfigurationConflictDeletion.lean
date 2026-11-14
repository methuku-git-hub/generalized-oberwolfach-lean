module

public import Mathlib.Data.Finset.Union
public import Mathlib.Tactic

@[expose] public section

/-! Deleting all configurations incident with a selected intersecting
pair. The loss is bounded in every fixed compatibility set at once. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C E : Type*} [DecidableEq C] [DecidableEq E]

def selectedConflictPairs (P : Finset (C×C)) (S : Finset C) : Finset (C×C) :=
  P.filter (fun z => z.1∈S ∧ z.2∈S)

def conflictEndpoints (P : Finset (C×C)) : Finset C := P.biUnion (fun z => {z.1,z.2})

def isolatedConfigurations (P : Finset (C×C)) (S : Finset C) : Finset C :=
  S\conflictEndpoints (selectedConflictPairs P S)

theorem conflictEndpoints_card (P : Finset (C×C)) :
    (conflictEndpoints P).card ≤ 2*P.card := by
  calc
    _ ≤ ∑ z∈P,({z.1,z.2}:Finset C).card := Finset.card_biUnion_le
    _ ≤ ∑ _z∈P,2 := Finset.sum_le_sum (by intro z _;exact Finset.card_le_two)
    _ = _ := by simp [Nat.mul_comm]

theorem isolatedConfigurations_subset (P : Finset (C×C)) (S : Finset C) :
    isolatedConfigurations P S ⊆ S := Finset.sdiff_subset

theorem isolatedConfigurations_pair_absent (P : Finset (C×C)) (S : Finset C)
    (a b : C) (ha : a∈isolatedConfigurations P S) (hb : b∈isolatedConfigurations P S) :
    (a,b)∉P := by
  intro hp
  have hh : (a,b)∈selectedConflictPairs P S :=
    Finset.mem_filter.mpr ⟨hp,(Finset.mem_sdiff.mp ha).1,(Finset.mem_sdiff.mp hb).1⟩
  apply (Finset.mem_sdiff.mp ha).2
  exact Finset.mem_biUnion.mpr ⟨(a,b),hh,by simp⟩

theorem isolatedConfigurations_disjoint (A : C → Finset E) (P : Finset (C×C)) (S : Finset C)
    (hP : ∀ a∈S,∀ b∈S,a≠b → ¬Disjoint (A a) (A b) → (a,b)∈P) :
    ∀ a∈isolatedConfigurations P S,∀ b∈isolatedConfigurations P S,a≠b → Disjoint (A a) (A b) := by
  intro a ha b hb hab
  by_contra h
  exact isolatedConfigurations_pair_absent P S a b ha hb
    (hP a (isolatedConfigurations_subset P S ha) b (isolatedConfigurations_subset P S hb) hab h)

theorem isolatedConfigurations_count_loss (P : Finset (C×C)) (S T : Finset C) :
    (S∩T).card ≤ (isolatedConfigurations P S∩T).card+2*(selectedConflictPairs P S).card := by
  have hsub : S∩T ⊆ (isolatedConfigurations P S∩T)∪conflictEndpoints (selectedConflictPairs P S) := by
    intro c hc
    by_cases h : c∈conflictEndpoints (selectedConflictPairs P S)
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hc).1,h⟩,(Finset.mem_inter.mp hc).2⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (conflictEndpoints_card _) _))

end Oberwolfach
