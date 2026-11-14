module

public import Oberwolfach.LocalFixedSupportWeights
public import Oberwolfach.CandidateResourceRestriction

@[expose] public section

/-! The weight on the enlarged ground set retains the original value
exactly when the support meets the prescribed additional set at most once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def extensionResourceWeight (R : C → Finset V) (w : C → ℝ) (A Z : Finset V) (C₀ : C) : ℝ :=
  if R C₀⊆A∪Z ∧ (R C₀∩Z).card ≤ 1 then w C₀ else 0

theorem extension_resource_root_support (R A Z : Finset V) (hAZ : Disjoint A Z)
    (v : V) (hv : v∈Z) (hvR : v∈R) :
    (R⊆A∪Z ∧ (R∩Z).card ≤ 1) ↔ R⊆insert v A := by
  constructor
  · rintro ⟨hR,hcard⟩ x hx
    rcases Finset.mem_union.mp (hR hx) with hA | hZ
    · exact Finset.mem_insert_of_mem hA
    · have he := Finset.card_le_one.mp hcard x (Finset.mem_inter.mpr ⟨hx,hZ⟩)
        v (Finset.mem_inter.mpr ⟨hvR,hv⟩)
      exact Finset.mem_insert.mpr (Or.inl he)
  · intro hR
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp (hR hx) with rfl | hA
      · exact Finset.mem_union_right _ hv
      · exact Finset.mem_union_left _ hA
    · apply Finset.card_le_one.mpr
      intro x hx y hy
      have he (x) (hx : x∈R∩Z) : x=v := by
        have hh := Finset.mem_insert.mp (hR (Finset.mem_inter.mp hx).1)
        exact hh.resolve_right (fun hA => Finset.disjoint_left.mp hAZ hA (Finset.mem_inter.mp hx).2)
      exact (he x hx).trans (he y hy).symm

theorem extension_resource_root_degree (R : C → Finset V) (w : C → ℝ)
    (A Z : Finset V) (hAZ : Disjoint A Z) (v : V) (hv : v∈Z) :
    hypergraphWeightedDegree R (extensionResourceWeight R w A Z) v=
      hypergraphWeightedDegree R (inducedResourceWeight R w (insert v A)) v := by
  unfold hypergraphWeightedDegree
  apply Finset.sum_congr rfl
  intro C₀ _
  by_cases hvR : v∈R C₀
  · simp only [hvR,ite_true,extensionResourceWeight,inducedResourceWeight]
    simp only [extension_resource_root_support (R C₀) A Z hAZ v hv hvR]
  · simp only [hvR,ite_false]

theorem extension_resource_degree_change (R : C → Finset V) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (A Z : Finset V) (hAZ : Disjoint A Z) (v : V) (hv : v∈A) :
    0 ≤ hypergraphWeightedDegree R (extensionResourceWeight R w A Z) v-
      hypergraphWeightedDegree R (inducedResourceWeight R w A) v ∧
    hypergraphWeightedDegree R (extensionResourceWeight R w A Z) v-
      hypergraphWeightedDegree R (inducedResourceWeight R w A) v ≤
      (Z.card:ℝ)*((J:ℝ)*((A∪Z).card:ℝ)^(c-2)*B) := by
  let u := inducedResourceWeight R w (A∪Z)
  have hu : ∀ C₀,0 ≤ u C₀ := inducedResourceWeight_nonneg R w (fun C₀ => (hw C₀).1) (A∪Z)
  have hbase (C₀) (hA : R C₀⊆A) : (R C₀∩Z).card ≤ 1 := by
    have he : R C₀∩Z=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact Finset.disjoint_left.mp hAZ (hA (Finset.mem_inter.mp hx).1) (Finset.mem_inter.mp hx).2
    simp [he]
  have hpoint (C₀) : 0 ≤
      (if v∈R C₀ then extensionResourceWeight R w A Z C₀ else 0)-
        (if v∈R C₀ then inducedResourceWeight R w A C₀ else 0) ∧
      (if v∈R C₀ then extensionResourceWeight R w A Z C₀ else 0)-
        (if v∈R C₀ then inducedResourceWeight R w A C₀ else 0) ≤
      if v∈R C₀ ∧ ∃ z : Z,z.val∈R C₀ then u C₀ else 0 := by
    by_cases hvR : v∈R C₀
    · simp only [hvR,ite_true,true_and]
      by_cases hA : R C₀⊆A
      · have hgood : R C₀⊆A∪Z ∧ (R C₀∩Z).card ≤ 1 := ⟨hA.trans Finset.subset_union_left,hbase C₀ hA⟩
        simp only [extensionResourceWeight,inducedResourceWeight,if_pos hgood,if_pos hA,sub_self]
        exact ⟨le_rfl,by split_ifs <;> first | exact hu C₀ | exact le_rfl⟩
      · simp only [inducedResourceWeight,if_neg hA,sub_zero]
        by_cases hgood : R C₀⊆A∪Z ∧ (R C₀∩Z).card ≤ 1
        · have hz : ∃ z : Z,z.val∈R C₀ := by
            obtain ⟨z,hz,hzA⟩ := Finset.not_subset.mp hA
            have hzZ := (Finset.mem_union.mp (hgood.1 hz)).resolve_left hzA
            exact ⟨⟨z,hzZ⟩,hz⟩
          simp only [extensionResourceWeight,if_pos hgood,if_pos hz,u,inducedResourceWeight,if_pos hgood.1]
          exact ⟨(hw C₀).1,le_rfl⟩
        · rw [extensionResourceWeight,if_neg hgood]
          exact ⟨le_rfl,by split_ifs <;> first | exact hu C₀ | exact le_rfl⟩
    · simp only [hvR,ite_false,false_and,sub_self,le_refl,and_self]
  have hlo := Finset.sum_nonneg (fun C₀ (_ : C₀∈Finset.univ) => (hpoint C₀).1)
  have hhi := Finset.sum_le_sum (fun C₀ (_ : C₀∈Finset.univ) => (hpoint C₀).2)
  rw [Finset.sum_sub_distrib] at hlo hhi
  refine ⟨hlo,hhi.trans ?_⟩
  calc
    _ ≤ ∑ z : Z,∑ C₀,if v∈R C₀ ∧ z.val∈R C₀ then u C₀ else 0 := by
      convert finite_weighted_union_bound u hu (fun C₀ => v∈R C₀) (fun C₀ (z : Z) => z.val∈R C₀) using 1 <;> congr!
    _ ≤ ∑ _z : Z,(J:ℝ)*((A∪Z).card:ℝ)^(c-2)*B := by
      apply Finset.sum_le_sum
      intro z _
      apply induced_resource_pair_weight R c J hc hR hJ w B hB (fun C₀ => (hw C₀).2) (A∪Z) v z.val
      intro he
      exact Finset.disjoint_left.mp hAZ hv (he.symm ▸ z.property)
    _ = _ := by simp

end Oberwolfach
