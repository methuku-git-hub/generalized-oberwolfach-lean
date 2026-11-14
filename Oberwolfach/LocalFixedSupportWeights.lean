module

public import Oberwolfach.InducedResourceWeights

@[expose] public section

/-! Local cycle counts with prescribed vertices, including the case
where a prescribed vertex is outside the selected ground set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

theorem uniform_resources_local_fixed_set_count (R : C → Finset V) (c J : ℕ)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (S Y : Finset V) (hS : S.card ≤ c) :
    Fintype.card {C₀ : C // S⊆R C₀ ∧ R C₀⊆Y} ≤ J*Y.card^(c-S.card) := by
  by_cases hSY : S⊆Y
  · exact uniform_resources_between_count R c J hR hJ S Y hSY hS
  · have hn (C₀ : C) : ¬(S⊆R C₀ ∧ R C₀⊆Y) := fun h => hSY (h.1.trans h.2)
    simp only [Fintype.card_subtype,hn,Finset.filter_false,Finset.card_empty,Nat.zero_le]

theorem induced_resource_fixed_set_weight (R : C → Finset V) (c J : ℕ)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,w C₀ ≤ B)
    (S Y : Finset V) (hS : S.card ≤ c) :
    (∑ C₀,if S⊆R C₀ then inducedResourceWeight R w Y C₀ else 0) ≤
      (J:ℝ)*(Y.card:ℝ)^(c-S.card)*B := by
  have hcount : (Fintype.card {C₀ : C // S⊆R C₀ ∧ R C₀⊆Y}:ℝ) ≤
      J*(Y.card:ℝ)^(c-S.card) := by exact_mod_cast uniform_resources_local_fixed_set_count R c J hR hJ S Y hS
  calc
    _ ≤ ∑ C₀,if S⊆R C₀ ∧ R C₀⊆Y then B else 0 := by
      apply Finset.sum_le_sum
      intro C₀ _
      by_cases h₁ : S⊆R C₀ <;> by_cases h₂ : R C₀⊆Y
      all_goals simp [h₁,h₂,inducedResourceWeight,hw C₀]
    _ = (Fintype.card {C₀ : C // S⊆R C₀ ∧ R C₀⊆Y}:ℝ)*B := by
      simp only [Fintype.card_subtype,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hB

theorem induced_resource_triple_weight (R : C → Finset V) (c J : ℕ) (hc : 3 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,w C₀ ≤ B)
    (Y : Finset V) (v x y : V) (hvx : v≠x) (hvy : v≠y) (hxy : x≠y) :
    (∑ C₀,if v∈R C₀ ∧ x∈R C₀ ∧ y∈R C₀ then inducedResourceWeight R w Y C₀ else 0) ≤
      (J:ℝ)*(Y.card:ℝ)^(c-3)*B := by
  have hcard : ({v,x,y} : Finset V).card=3 := by simp [hvx,hvy,hxy]
  have hh := induced_resource_fixed_set_weight R c J hR hJ w B hB hw {v,x,y} Y (by simpa only [hcard] using hc)
  simpa only [hcard,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hh

end Oberwolfach
