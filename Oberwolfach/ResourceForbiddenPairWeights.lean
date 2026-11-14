module

public import Oberwolfach.LocalFixedSupportWeights
public import Oberwolfach.FiniteSubsetSums

@[expose] public section

/-! Weighted-degree losses from forbidding displayed endpoint pairs.
The original weight of every retained cycle is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

def pairRestrictedResourceWeight (R : C → Finset V) (w : C → ℝ) (E : Finset (V×V)) (C₀ : C) : ℝ :=
  if ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀) then w C₀ else 0

theorem induced_resource_root_pair_weight (R : C → Finset V) (c J : ℕ) (hc : 3 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,w C₀ ≤ B)
    (Y : Finset V) (v x y : V) (hxy : x≠y) :
    (∑ C₀,if v∈R C₀ ∧ x∈R C₀ ∧ y∈R C₀ then inducedResourceWeight R w Y C₀ else 0) ≤
      if v=x ∨ v=y then (J:ℝ)*(Y.card:ℝ)^(c-2)*B else (J:ℝ)*(Y.card:ℝ)^(c-3)*B := by
  by_cases hvx : v=x
  · subst v
    simpa only [true_or,ite_true,and_self_left] using
      induced_resource_pair_weight R c J (by omega) hR hJ w B hB hw Y x y hxy
  · by_cases hvy : v=y
    · subst v
      have he (C₀ : C) : (y∈R C₀ ∧ x∈R C₀ ∧ y∈R C₀) ↔ (x∈R C₀ ∧ y∈R C₀) := by tauto
      simp only [he,or_true,ite_true]
      exact induced_resource_pair_weight R c J (by omega) hR hJ w B hB hw Y x y hxy
    · rw [if_neg (not_or.mpr ⟨hvx,hvy⟩)]
      exact induced_resource_triple_weight R c J hc hR hJ w B hB hw Y v x y hvx hvy hxy

theorem resource_forbidden_pairs_degree_loss (R : C → Finset V) (c J : ℕ) (hc : 3 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (Y : Finset V) (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (v : V) :
    0 ≤ hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v ∧
    hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v ≤
      ((E.filter (fun e => v=e.1 ∨ v=e.2)).card:ℝ)*((J:ℝ)*(Y.card:ℝ)^(c-2)*B)+
      ((E.filter (fun e => ¬(v=e.1 ∨ v=e.2))).card:ℝ)*((J:ℝ)*(Y.card:ℝ)^(c-3)*B) := by
  let u := inducedResourceWeight R w Y
  have hu : ∀ C₀,0 ≤ u C₀ := inducedResourceWeight_nonneg R w (fun C₀ => (hw C₀).1) Y
  have he : hypergraphWeightedDegree R u v-hypergraphWeightedDegree R (pairRestrictedResourceWeight R u E) v=
      ∑ C₀,if v∈R C₀ ∧ ∃ e : E,e.val.1∈R C₀ ∧ e.val.2∈R C₀ then u C₀ else 0 := by
    unfold hypergraphWeightedDegree
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro C₀ _
    by_cases hv : v∈R C₀
    · simp only [hv,ite_true,true_and]
      unfold pairRestrictedResourceWeight
      by_cases hg : ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)
      · rw [if_pos hg,if_neg (not_exists.mpr hg),sub_self]
      · have hb : ∃ e : E,e.val.1∈R C₀ ∧ e.val.2∈R C₀ := by
          simpa only [not_forall,not_not] using hg
        rw [if_neg hg,if_pos hb,sub_zero]
    · simp only [hv,ite_false,false_and,sub_self]
  change 0 ≤ _ ∧ _ ≤ _
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun C₀ _ => by split_ifs <;> first | exact hu C₀ | exact le_rfl)
  · have hh := finite_weighted_union_bound u hu (fun C₀ => v∈R C₀)
      (fun C₀ (e : E) => e.val.1∈R C₀ ∧ e.val.2∈R C₀)
    calc
      _ ≤ ∑ e : E,∑ C₀,if v∈R C₀ ∧ e.val.1∈R C₀ ∧ e.val.2∈R C₀ then u C₀ else 0 := by
        convert hh using 1 <;> congr!
      _ ≤ ∑ e : E,if v=e.val.1 ∨ v=e.val.2 then
          (J:ℝ)*(Y.card:ℝ)^(c-2)*B else (J:ℝ)*(Y.card:ℝ)^(c-3)*B := by
        apply Finset.sum_le_sum
        intro e _
        exact induced_resource_root_pair_weight R c J hc hR hJ w B hB (fun C₀ => (hw C₀).2)
          Y v e.val.1 e.val.2 (hE e.val e.property)
      _ = _ := by
        convert finite_subset_ite_sum E (fun e => v=e.1 ∨ v=e.2)
          ((J:ℝ)*(Y.card:ℝ)^(c-2)*B) ((J:ℝ)*(Y.card:ℝ)^(c-3)*B) using 1 <;> congr!

end Oberwolfach
