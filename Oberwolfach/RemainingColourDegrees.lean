module

public import Oberwolfach.NeighbourColourCertificates
public import Oberwolfach.NibbleAvailableColours

@[expose] public section

/-! The number of uncoloured vertices at which a colour is still available
in the specified neighbouring cliques. The telescoping identity uses the
same original configurations and includes the uncoloured-vertex condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem clique_no_retained_iff_card
    {V C J : Type*} (G : SimpleGraph V) (Q : Finset J) (T : J → Finset V)
    (hT : ∀ j∈Q,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (σ : V → C×Bool) (c : C) :
    (∀ j∈Q,∀ v∈T j,coinRetainedColour G σ v≠some c) ↔
      (assignedSetIndices Q T σ c).card=(rejectedSetIndices G Q T σ c).card := by
  classical
  have h := nibbleAvailableColours_mem_iff G Q T hT {c} σ c
  simpa only [nibbleAvailableColours,Finset.mem_filter,Finset.mem_singleton,
    true_and] using h

def remainingColourVertices {V C J : Type*} (G : SimpleGraph V)
    (U : Finset V) (Q : V → Finset J) (T : J → Finset V) (c : C)
    (σ : V → C×Bool) : Finset V :=
  U.filter (fun v=>¬coinColourSurvives G σ v ∧
    ∀ j∈Q v,∀ w∈T j,coinRetainedColour G σ w≠some c)

theorem remainingColourVertices_card
    {V C J : Type*} (G : SimpleGraph V) (U : Finset V)
    (Q : V → Finset J) (T : J → Finset V) {k : ℕ}
    (hQ : ∀ v∈U,(Q v).card≤k)
    (hT : ∀ v∈U,∀ j∈Q v,∀ u∈T j,∀ w∈T j,u≠w → G.Adj u w)
    (σ : V → C×Bool) (c : C) :
    ((remainingColourVertices G U Q T c σ).card : ℝ)=
      ∑ a∈Finset.range (k+1),
        (neighbourColourCount G U Q T c a a σ-
          neighbourColourCount G U Q T c (a+1) a σ) := by
  classical
  let D := U.filter (fun v=>¬coinColourSurvives G σ v)
  have hc (a b : ℕ) : neighbourColourCount G U Q T c a b σ=
      ∑ v∈D,if a≤(assignedSetIndices (Q v) T σ c).card ∧
        b≤(rejectedSetIndices G (Q v) T σ c).card then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    apply congrArg (fun n : ℕ=>(n : ℝ))
    apply congrArg Finset.card
    ext v
    simp [filteredCoinConflictSet,coinConflictSet,
      neighbourColourPredicate,D,and_comm,and_left_comm,and_assoc]
  have hcard : ((remainingColourVertices G U Q T c σ).card : ℝ)=
      ∑ v∈D,if (assignedSetIndices (Q v) T σ c).card=
        (rejectedSetIndices G (Q v) T σ c).card then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    apply congrArg (fun n : ℕ=>(n : ℝ))
    apply congrArg Finset.card
    ext v
    simp only [remainingColourVertices,D,Finset.mem_filter]
    by_cases hv : v∈U
    · simp only [hv,true_and]
      exact and_congr_right (fun _=>clique_no_retained_iff_card G (Q v) T (hT v hv) σ c)
    · simp [hv]
  rw [hcard]
  simp_rw [hc,← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  exact (threshold_diagonal_sum
    (Finset.card_le_card (rejectedSetIndices_subset_assigned G (Q v) T σ c))
    ((Finset.card_le_card (Finset.filter_subset _ _)).trans
      (hQ v (Finset.mem_filter.mp hv).1))).symm

end Oberwolfach
