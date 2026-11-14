module

public import Oberwolfach.NormalizedSubsetCounts

@[expose] public section

/-! Transfer a subset sampled inside B back to the ambient vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem subtype_sample_subset {V : Type*} (B : Finset V) (S : Finset {x // x ∈ B}) :
    S.map (Function.Embedding.subtype _) ⊆ B := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
  exact y.2

theorem subtype_sample_intersection_card {V : Type*} (A B : Finset V)
    [DecidableEq {x // x ∈ B}] (S : Finset {x // x ∈ B}) :
    ((A.subtype (fun x => x ∈ B)) ∩ S).card =
      (A ∩ S.map (Function.Embedding.subtype _)).card := by
  have he : (((A.subtype (fun x => x ∈ B)) ∩ S).map (Function.Embedding.subtype _)) =
      A ∩ S.map (Function.Embedding.subtype _) := by
    rw [Finset.map_inter, Finset.subtype_map, Finset.filter_mem_eq_inter]
    ext x
    simp only [Finset.mem_inter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, subtype_sample_subset B S h.2⟩, h.2⟩
  rw [← he, Finset.card_map]

theorem subtype_restriction_card {V : Type*} (A B : Finset V) :
    (A.subtype (fun x => x ∈ B)).card = (A ∩ B).card := by
  rw [Finset.card_subtype, Finset.filter_mem_eq_inter]

end Oberwolfach
