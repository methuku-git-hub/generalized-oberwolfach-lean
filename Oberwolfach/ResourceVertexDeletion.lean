module

public import Oberwolfach.HypergraphWeightMoments
public import Oberwolfach.OrdinaryCycleConflictLoss

@[expose] public section

/-! Restriction to cycles avoiding a prescribed vertex set. The exact
realised loss is charged to pair weights; no sampling factor is inserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

def vertexRestrictedWeight (R : C → Finset V) (w : C → ℝ) (Z : Finset V) (C₀ : C) : ℝ :=
  if Disjoint (R C₀) Z then w C₀ else 0

theorem resource_vertex_deletion_degree (R : C → Finset V) (w : C → ℝ) (hw : ∀ C₀,0 ≤ w C₀)
    (K : ℝ) (hpair : ∀ u v,u≠v → (∑ C₀,if u∈R C₀ ∧ v∈R C₀ then w C₀ else 0) ≤ K)
    (Z : Finset V) (x : V) (hx : x∉Z) :
    0 ≤ hypergraphWeightedDegree R w x-hypergraphWeightedDegree R (vertexRestrictedWeight R w Z) x ∧
    hypergraphWeightedDegree R w x-hypergraphWeightedDegree R (vertexRestrictedWeight R w Z) x ≤ Z.card*K := by
  have hhit (C₀ : C) : ¬Disjoint (R C₀) Z ↔ ∃ z : Z,z.val∈R C₀ := by
    constructor
    · intro hd
      by_contra hn
      apply hd
      exact Finset.disjoint_left.mpr (fun v hv hz => hn ⟨⟨v,hz⟩,hv⟩)
    · rintro ⟨z,hz⟩ hd
      exact Finset.disjoint_left.mp hd hz z.property
  have he : hypergraphWeightedDegree R w x-hypergraphWeightedDegree R (vertexRestrictedWeight R w Z) x=
      ∑ C₀,if x∈R C₀ ∧ ∃ z : Z,z.val∈R C₀ then w C₀ else 0 := by
    unfold hypergraphWeightedDegree
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro C₀ _
    by_cases h : x∈R C₀ <;> by_cases hd : Disjoint (R C₀) Z
    · have hh : ¬∃ z : Z,z.val∈R C₀ := fun hz => (hhit C₀).mpr hz hd
      simp [vertexRestrictedWeight,h,hd,hh]
    · have hh := (hhit C₀).mp hd
      simp [vertexRestrictedWeight,h,hd,hh]
    all_goals simp [vertexRestrictedWeight,h]
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun C₀ _ => by split_ifs <;> first | exact hw C₀ | exact le_refl _)
  · have hh := finite_weighted_union_bound w hw (fun C₀ => x∈R C₀) (fun C₀ (z : Z) => z.val∈R C₀)
    calc
      _ ≤ ∑ z : Z,∑ C₀,if x∈R C₀ ∧ z.val∈R C₀ then w C₀ else 0 := by
        convert hh using 1 <;> congr!
      _ ≤ ∑ _z : Z,K := Finset.sum_le_sum (fun z _ => hpair x z.val (by intro he;exact hx (he ▸ z.property)))
      _ = _ := by simp

theorem resource_vertex_deletion_load_error (R : C → Finset V) (w : C → ℝ) (hw : ∀ C₀,0 ≤ w C₀)
    (K η : ℝ) (hK : 0 ≤ K)
    (hpair : ∀ u v,u≠v → (∑ C₀,if u∈R C₀ ∧ v∈R C₀ then w C₀ else 0) ≤ K)
    (herr : ∀ v,|1-hypergraphWeightedDegree R w v| ≤ η)
    (Z : Finset V) (x : V) (hx : x∉Z) :
    |1-hypergraphWeightedDegree R (vertexRestrictedWeight R w Z) x| ≤ η+Z.card*K := by
  obtain ⟨h₀,h₁⟩ := resource_vertex_deletion_degree R w hw K hpair Z x hx
  have he := abs_le.mp (herr x)
  have hn : 0 ≤ (Z.card:ℝ)*K := mul_nonneg (Nat.cast_nonneg _) hK
  apply abs_le.mpr
  constructor <;> linarith

end Oberwolfach
