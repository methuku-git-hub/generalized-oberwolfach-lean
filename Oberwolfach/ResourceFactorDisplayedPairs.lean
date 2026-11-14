module

public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Displayed endpoint pairs of vertex-disjoint indexed cycles.
Incidence bounds are proved on their actual union, not assumed anew. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

theorem resource_factor_pairs_card (R : C → Finset V) (F : C → Finset (V×V)) (M : Finset C)
    (hM : ∀ C₀∈M,∀ D∈M,C₀≠D → Disjoint (R C₀) (R D))
    (hsize : ∀ C₀∈M,(F C₀).card ≤ (R C₀).card) :
    (M.biUnion F).card ≤ (M.biUnion R).card := by
  have hdis : (M : Set C).PairwiseDisjoint R := by
    intro x hx y hy hxy
    exact hM x hx y hy hxy
  calc
    _ ≤ ∑ C₀∈M,(F C₀).card := Finset.card_biUnion_le
    _ ≤ ∑ C₀∈M,(R C₀).card := Finset.sum_le_sum hsize
    _ = _ := (Finset.card_biUnion hdis).symm

theorem resource_factor_pairs_incidence (R : C → Finset V) (F : C → Finset (V×V)) (M : Finset C)
    (hM : ∀ C₀∈M,∀ D∈M,C₀≠D → Disjoint (R C₀) (R D))
    (hF : ∀ C₀∈M,∀ e∈F C₀,e.1∈R C₀ ∧ e.2∈R C₀)
    (d : ℕ) (hd : ∀ C₀∈M,∀ v,((F C₀).filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d) (v : V) :
    ((M.biUnion F).filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d := by
  by_cases hx : ∃ C₀∈M,v∈R C₀
  · obtain ⟨C₀,hC,hv⟩ := hx
    have hs : (M.biUnion F).filter (fun e => v=e.1 ∨ v=e.2) ⊆
        (F C₀).filter (fun e => v=e.1 ∨ v=e.2) := by
      intro e he
      obtain ⟨he,hve⟩ := Finset.mem_filter.mp he
      obtain ⟨D,hD,heD⟩ := Finset.mem_biUnion.mp he
      have hvD : v∈R D := by
        rcases hve with h | h
        · exact h ▸ (hF D hD e heD).1
        · exact h ▸ (hF D hD e heD).2
      have hDC : D=C₀ := by
        by_contra hh
        exact Finset.disjoint_left.mp (hM D hD C₀ hC hh) hvD hv
      subst D
      exact Finset.mem_filter.mpr ⟨heD,hve⟩
    exact (Finset.card_le_card hs).trans (hd C₀ hC v)
  · have hz : (M.biUnion F).filter (fun e => v=e.1 ∨ v=e.2)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,hve⟩ := Finset.mem_filter.mp he
      obtain ⟨D,hD,heD⟩ := Finset.mem_biUnion.mp he
      have hvD : v∈R D := by
        rcases hve with h | h
        · exact h ▸ (hF D hD e heD).1
        · exact h ▸ (hF D hD e heD).2
      exact hx ⟨D,hD,hvD⟩
    rw [hz,Finset.card_empty]
    exact Nat.zero_le _

theorem resource_pair_avoidance_disjoint (R : C → Finset V) (F : C → Finset (V×V))
    (M : Finset C) (E : Finset (V×V))
    (hF : ∀ C₀∈M,∀ e∈F C₀,e.1∈R C₀ ∧ e.2∈R C₀)
    (havoid : ∀ C₀∈M,∀ e∈E,¬(e.1∈R C₀ ∧ e.2∈R C₀)) :
    Disjoint E (M.biUnion F) := by
  apply Finset.disjoint_left.mpr
  intro e he hM
  obtain ⟨C₀,hC,heC⟩ := Finset.mem_biUnion.mp hM
  exact havoid C₀ hC e he (hF C₀ hC e heC)

end Oberwolfach
