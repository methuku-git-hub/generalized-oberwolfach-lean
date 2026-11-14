module

public import Oberwolfach.FiniteSupportCounts

@[expose] public section

/-! Counts of forbidden displayed pairs incident with a specified
vertex set. An edge counted at both endpoints only improves the bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_pairs_incident_set_card {V : Type*} [DecidableEq V]
    (E : Finset (V×V)) (X : Finset V) (d : ℕ)
    (hd : ∀ v∈X,(E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d) :
    (E.filter (fun e => e.1∈X ∨ e.2∈X)).card ≤ X.card*d := by
  have hs : E.filter (fun e => e.1∈X ∨ e.2∈X) ⊆
      X.biUnion (fun v => E.filter (fun e => v=e.1 ∨ v=e.2)) := by
    intro e he
    obtain ⟨he,hx⟩ := Finset.mem_filter.mp he
    rcases hx with hx | hx
    · exact Finset.mem_biUnion.mpr ⟨e.1,hx,Finset.mem_filter.mpr ⟨he,Or.inl rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨e.2,hx,Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩⟩
  calc
    _ ≤ (X.biUnion (fun v => E.filter (fun e => v=e.1 ∨ v=e.2))).card := Finset.card_le_card hs
    _ ≤ ∑ v∈X,(E.filter (fun e => v=e.1 ∨ v=e.2)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v∈X,d := Finset.sum_le_sum hd
    _ = _ := by simp

end Oberwolfach
