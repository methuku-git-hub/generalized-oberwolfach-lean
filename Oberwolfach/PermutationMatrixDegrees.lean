module

public import Oberwolfach.PermutationMatrixCuts

@[expose] public section

/-! Exact row and column error budgets for deleting permutation-close arcs,
including the auxiliary diagonal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

theorem permutationSeparatedMatrix_row_loss (π : Equiv.Perm V) (b : ℕ)
    (M : V→V→ℕ) (hM : ∀ x y,M x y≤1) (x : V) :
    |((∑ y,permutationSeparatedMatrix π b M x y:ℕ):ℝ)-(∑ y,M x y:ℕ)|≤2*(b:ℝ)+1 := by
  have hh := permutationSeparatedMatrix_cut_loss π b M hM {x} Finset.univ
  have hn : 1≤Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hn' : (1:ℝ)≤Fintype.card V := by exact_mod_cast hn
  simp only [matrixCut,Finset.sum_singleton,Finset.card_singleton,Finset.card_univ,Nat.cast_one,min_eq_left hn'] at hh
  have hsub : (∑ y,permutationSeparatedMatrix π b M x y)≤∑ y,M x y := by
    apply Finset.sum_le_sum
    intro y _
    simp only [permutationSeparatedMatrix]
    split_ifs <;> omega
  have hsub' : ((∑ y,permutationSeparatedMatrix π b M x y:ℕ):ℝ)≤(∑ y,M x y:ℕ) := by exact_mod_cast hsub
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hsub')]
  linarith only [hh]

theorem permutationSeparatedMatrix_column_loss (π : Equiv.Perm V) (b : ℕ)
    (M : V→V→ℕ) (hM : ∀ x y,M x y≤1) (y : V) :
    |((∑ x,permutationSeparatedMatrix π b M x y:ℕ):ℝ)-(∑ x,M x y:ℕ)|≤2*(b:ℝ)+1 := by
  have hh := permutationSeparatedMatrix_row_loss π b (fun x y=>M y x) (fun x y=>hM y x) y
  simpa only [permutationSeparatedMatrix,permutationClose_symm π b] using hh

end Oberwolfach
