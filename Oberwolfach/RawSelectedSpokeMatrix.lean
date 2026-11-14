module

public import Oberwolfach.RawSelectedCutCounts
public import Oberwolfach.RawIntervalSelectedLabels
public import Oberwolfach.RawIntervalSelectedNeighbours

@[expose] public section

/-! The actual bipartite adjacency matrix of an selected ordinary or interval label.
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

def rawSelectedSpokeMatrix (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Γ⊕Color) (v : V) (u : U) : ℕ :=
  if rawIntervalFamilyState π d σ (v,u)=some j then 1 else 0

theorem rawSelectedSpokeMatrix_le_one (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Γ⊕Color) (v : V) (u : U) :
    rawSelectedSpokeMatrix π d σ j v u≤1 := by unfold rawSelectedSpokeMatrix;split_ifs <;> omega

theorem rawSelectedSpokeMatrix_row (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Γ⊕Color) (v : V) :
    ((∑ u,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)=rawIntervalSelectedLabelCount π d σ (fun _=>j) {v} := by
  simp only [rawSelectedSpokeMatrix,rawIntervalSelectedLabelCount,Finset.mem_singleton,forall_eq,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem rawSelectedSpokeMatrix_col (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Γ⊕Color) (u : U) :
    ((∑ v,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)=rawIntervalSelectedNeighbourCount π d σ (fun _=>j) Finset.univ {u} := by
  simp only [rawSelectedSpokeMatrix,rawIntervalSelectedNeighbourCount,Finset.mem_singleton,forall_eq,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem rawSelectedSpokeMatrix_row_card (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Γ⊕Color) (v : V) :
    (∑ u,rawSelectedSpokeMatrix π d σ j v u)=
      Fintype.card {u : U // rawIntervalFamilyState π d σ (v,u)=some j} := by
  simp only [rawSelectedSpokeMatrix,Fintype.card_subtype,Finset.card_filter]

theorem rawSelectedSpokeMatrix_cut (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (j : Γ⊕Color) (X : Finset V) (Y : Finset U) :
    ((∑ v∈X,∑ u∈Y,rawSelectedSpokeMatrix π d σ j v u:ℕ):ℝ)=rawSelectedCutCount π d σ j X Y := by
  simp only [rawSelectedSpokeMatrix,rawSelectedCutCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

end Oberwolfach
