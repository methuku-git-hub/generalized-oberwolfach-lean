module

public import Oberwolfach.RawIntervalCutCounts
public import Oberwolfach.RawIntervalLabelCounts
public import Oberwolfach.RawOrdinaryHubCounts

@[expose] public section

/-! The actual bipartite adjacency matrix of an ordinary interval label.
All count identities use this single matrix, with no independent-spoke
replacement or later change of coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawIntervalSpokeMatrix (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (v : V) (u : U) : ℕ :=
  if rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j) then 1 else 0

theorem rawIntervalSpokeMatrix_le_one (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (v : V) (u : U) :
    rawIntervalSpokeMatrix π d σ j v u≤1 := by unfold rawIntervalSpokeMatrix;split_ifs <;> omega

theorem rawIntervalSpokeMatrix_row (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (v : V) :
    ((∑ u,rawIntervalSpokeMatrix π d σ j v u:ℕ):ℝ)=rawIntervalLabelCount π d σ j {v} := by
  simp only [rawIntervalSpokeMatrix,rawIntervalLabelCount,Finset.mem_singleton,forall_eq,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem rawIntervalSpokeMatrix_col (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (u : U) :
    ((∑ v,rawIntervalSpokeMatrix π d σ j v u:ℕ):ℝ)=rawIntervalNeighbourCount π d σ j Finset.univ {u} := by
  simp only [rawIntervalSpokeMatrix,rawIntervalNeighbourCount,Finset.mem_singleton,forall_eq,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem rawIntervalSpokeMatrix_row_card (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (v : V) :
    (∑ u,rawIntervalSpokeMatrix π d σ j v u)=
      Fintype.card {u : U // rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j)} := by
  simp only [rawIntervalSpokeMatrix,Fintype.card_subtype,Finset.card_filter]

theorem rawIntervalSpokeMatrix_cut (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Color) (X : Finset V) (Y : Finset U) :
    ((∑ v∈X,∑ u∈Y,rawIntervalSpokeMatrix π d σ j v u:ℕ):ℝ)=rawIntervalCutCount π d σ j X Y := by
  simp only [rawIntervalSpokeMatrix,rawIntervalCutCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

end Oberwolfach
