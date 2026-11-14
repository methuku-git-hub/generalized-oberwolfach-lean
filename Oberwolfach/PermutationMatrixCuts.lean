module

public import Oberwolfach.DirectedCutBounds
public import Oberwolfach.PermutationClose

@[expose] public section

/-! Column permutations preserve cut counts exactly. Removing auxiliary
arcs at permutation distance at most b costs at most (2b+1) times the
smaller side, including auxiliary diagonal entries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem matrixCut_permute_columns {V : Type*} [DecidableEq V]
    (M : V→V→ℕ) (τ : Equiv.Perm V) (S T : Finset V) :
    matrixCut (fun x y=>M x (τ y)) S T=matrixCut M S (T.image τ) := by
  unfold matrixCut
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_image]
  exact fun x _ y _ h=>τ.injective h

def permutationSeparatedMatrix {V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (M : V→V→ℕ) (x y : V) : ℕ := if PermutationClose π b x y then 0 else M x y

theorem permutationSeparatedMatrix_le_one {V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (M : V→V→ℕ) (hM : ∀ x y,M x y≤1) (x y : V) :
    permutationSeparatedMatrix π b M x y≤1 := by
  unfold permutationSeparatedMatrix
  split_ifs
  · omega
  · exact hM x y

theorem permutationSeparatedMatrix_cut_loss {V : Type*} [Fintype V]
    (π : Equiv.Perm V) (b : ℕ) (M : V→V→ℕ) (hM : ∀ x y,M x y≤1)
    (S T : Finset V) :
    (matrixCut M S T:ℝ)-(2*(b:ℝ)+1)*min (S.card:ℝ) T.card≤
      (matrixCut (permutationSeparatedMatrix π b M) S T:ℝ) := by
  let W := fun x y=>if PermutationClose π b x y then (1:ℕ) else 0
  have hrow (x : V) : ((∑ y,W x y:ℕ):ℝ)≤2*(b:ℝ)+1 := by
    have h := permutationClose_neighbour_card π b x
    simp only [Fintype.card_subtype,Finset.card_filter] at h
    exact_mod_cast h
  have hcol (y : V) : ((∑ x,W x y:ℕ):ℝ)≤2*(b:ℝ)+1 := by
    simpa only [W,permutationClose_symm π b] using hrow y
  exact matrixCut_loss_bound M (permutationSeparatedMatrix π b M) W
    (by intro x y;dsimp [W,permutationSeparatedMatrix];split_ifs <;> simp_all)
    hrow hcol S T

end Oberwolfach
