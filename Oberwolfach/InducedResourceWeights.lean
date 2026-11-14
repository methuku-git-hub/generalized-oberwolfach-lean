module

public import Oberwolfach.UniformResourceGroundCounts
public import Oberwolfach.ResourceVertexDeletion

@[expose] public section

/-! Induced resource weights retain the supplied weight on each
surviving identifier. Local pair estimates use the selected ground size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

def inducedResourceWeight (R : C → Finset V) (w : C → ℝ) (A : Finset V) (C₀ : C) : ℝ :=
  if R C₀⊆A then w C₀ else 0

theorem inducedResourceWeight_nonneg (R : C → Finset V) (w : C → ℝ)
    (hw : ∀ C₀,0 ≤ w C₀) (A : Finset V) (C₀ : C) : 0 ≤ inducedResourceWeight R w A C₀ := by
  dsimp [inducedResourceWeight];split_ifs <;> first | exact hw C₀ | exact le_rfl

theorem induced_resource_pair_weight (R : C → Finset V) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,w C₀ ≤ B)
    (A : Finset V) (u v : V) (huv : u≠v) :
    (∑ C₀,if u∈R C₀ ∧ v∈R C₀ then inducedResourceWeight R w A C₀ else 0) ≤
      (J:ℝ)*(A.card:ℝ)^(c-2)*B := by
  by_cases hu : u∈A
  swap
  · have hz (C₀ : C) : (if u∈R C₀ ∧ v∈R C₀ then inducedResourceWeight R w A C₀ else 0)=0 := by
      by_cases hs : R C₀⊆A
      · have hnu : u∉R C₀ := fun hh => hu (hs hh)
        simp [hnu]
      · simp [inducedResourceWeight,hs]
    simp only [hz,Finset.sum_const_zero]
    positivity
  by_cases hv : v∈A
  swap
  · have hz (C₀ : C) : (if u∈R C₀ ∧ v∈R C₀ then inducedResourceWeight R w A C₀ else 0)=0 := by
      by_cases hs : R C₀⊆A
      · have hnv : v∉R C₀ := fun hh => hv (hs hh)
        simp [hnv]
      · simp [inducedResourceWeight,hs]
    simp only [hz,Finset.sum_const_zero]
    positivity
  have hcount : (Fintype.card {C₀ : C // u∈R C₀ ∧ v∈R C₀ ∧ R C₀⊆A}:ℝ) ≤
      J*(A.card:ℝ)^(c-2) := by exact_mod_cast uniform_resources_local_pair_count R c J hc hR hJ A u v hu hv huv
  calc
    _ ≤ ∑ C₀,if u∈R C₀ ∧ v∈R C₀ ∧ R C₀⊆A then B else 0 := by
      apply Finset.sum_le_sum
      intro C₀ _
      by_cases h₁ : u∈R C₀ <;> by_cases h₂ : v∈R C₀ <;> by_cases h₃ : R C₀⊆A
      all_goals simp [h₁,h₂,h₃,inducedResourceWeight,hw C₀]
    _ = (Fintype.card {C₀ : C // u∈R C₀ ∧ v∈R C₀ ∧ R C₀⊆A}:ℝ)*B := by
      simp only [Fintype.card_subtype,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount hB

theorem inducedResourceWeight_delete (R : C → Finset V) (w : C → ℝ) (A U : Finset V)
    (hAU : A⊆U) :
    vertexRestrictedWeight R (inducedResourceWeight R w U) (U\A)=inducedResourceWeight R w A := by
  funext C₀
  by_cases hA : R C₀⊆A
  · have hU := hA.trans hAU
    have hd : Disjoint (R C₀) (U\A) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw;exact (Finset.mem_sdiff.mp hw).2 (hA hv)
    simp [vertexRestrictedWeight,inducedResourceWeight,hA,hU,hd]
  · by_cases hU : R C₀⊆U
    · have hd : ¬Disjoint (R C₀) (U\A) := by
        intro hd
        apply hA
        intro v hv
        by_contra hn
        exact Finset.disjoint_left.mp hd hv (Finset.mem_sdiff.mpr ⟨hU hv,hn⟩)
      simp [vertexRestrictedWeight,inducedResourceWeight,hA,hU,hd]
    · simp [vertexRestrictedWeight,inducedResourceWeight,hA,hU]

theorem induced_resource_degree_exchange (R : C → Finset V) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (A D : Finset V) (v : V) (hvA : v∈A) (hvD : v∈D) :
    |hypergraphWeightedDegree R (inducedResourceWeight R w A) v-
      hypergraphWeightedDegree R (inducedResourceWeight R w D) v| ≤
      ((A\D).card+(D\A).card:ℕ)*(J:ℝ)*((A∪D).card:ℝ)^(c-2)*B := by
  let K := (J:ℝ)*((A∪D).card:ℝ)^(c-2)*B
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hp := induced_resource_pair_weight R c J hc hR hJ w B hB (fun C₀ => (hw C₀).2) (A∪D)
  have hA := resource_vertex_deletion_degree R (inducedResourceWeight R w (A∪D))
    (inducedResourceWeight_nonneg R w (fun C₀ => (hw C₀).1) _) K hp ((A∪D)\A) v (by simp [hvA])
  have hD := resource_vertex_deletion_degree R (inducedResourceWeight R w (A∪D))
    (inducedResourceWeight_nonneg R w (fun C₀ => (hw C₀).1) _) K hp ((A∪D)\D) v (by simp [hvD])
  rw [inducedResourceWeight_delete R w A (A∪D) Finset.subset_union_left] at hA
  rw [inducedResourceWeight_delete R w D (A∪D) Finset.subset_union_right] at hD
  have heA : (A∪D)\A=D\A := by ext x;simp only [Finset.mem_sdiff,Finset.mem_union];tauto
  have heD : (A∪D)\D=A\D := by ext x;simp only [Finset.mem_sdiff,Finset.mem_union];tauto
  rw [heA] at hA
  rw [heD] at hD
  have h₁ : 0 ≤ ((D\A).card:ℝ)*K := by positivity
  have h₂ : 0 ≤ ((A\D).card:ℝ)*K := by positivity
  have he : (((A\D).card+(D\A).card:ℕ):ℝ)*(J:ℝ)*((A∪D).card:ℝ)^(c-2)*B=
      ((A\D).card:ℝ)*K+((D\A).card:ℝ)*K := by dsimp [K];push_cast;ring
  rw [he]
  apply abs_le.mpr
  constructor <;> linarith [hA.1,hA.2,hD.1,hD.2]

end Oberwolfach
