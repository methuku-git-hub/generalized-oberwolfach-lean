module

public import Oberwolfach.GraphCuts

@[expose] public section

/-! Directed cuts on the original labels. Bounds use row and column sums,
including cuts whose two sides overlap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def matrixCut {V : Type*} (M : V → V → ℕ) (S T : Finset V) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ T, M x y

theorem matrixCut_transpose {V : Type*} (M : V → V → ℕ) (S T : Finset V) :
    matrixCut M S T = matrixCut (fun x y => M y x) T S := by
  exact Finset.sum_comm

theorem matrixCut_row_lower {V : Type*} [Fintype V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1) (S T : Finset V) {d : ℝ}
    (hrow : ∀ x ∈ S, d ≤ ((∑ y, M x y : ℕ) : ℝ)) :
    (S.card : ℝ) * (d + T.card - Fintype.card V) ≤ (matrixCut M S T : ℝ) := by
  have hpoint (x : V) (hx : x ∈ S) :
      d + T.card - Fintype.card V ≤ ((∑ y ∈ T, M x y : ℕ) : ℝ) := by
    have hc : ∑ y ∈ Finset.univ \ T, M x y ≤ Fintype.card V - T.card := by
      calc
        _ ≤ ∑ _y ∈ Finset.univ \ T, 1 := Finset.sum_le_sum (fun y _ => hM x y)
        _ = _ := by simp [Finset.card_sdiff_of_subset (Finset.subset_univ T)]
    have hs := Finset.sum_sdiff (f := fun y => M x y) (Finset.subset_univ T)
    have ht := Finset.card_le_univ T
    have hcr : ((∑ y ∈ Finset.univ \ T, M x y : ℕ) : ℝ) ≤
        (Fintype.card V : ℝ) - T.card := by
      exact_mod_cast hc
    have hsr : ((∑ y ∈ Finset.univ \ T, M x y : ℕ) : ℝ) +
        ((∑ y ∈ T, M x y : ℕ) : ℝ) = ((∑ y, M x y : ℕ) : ℝ) := by
      exact_mod_cast hs
    linarith [hrow x hx]
  simpa only [matrixCut, Nat.cast_sum, Finset.sum_const, nsmul_eq_mul] using
    Finset.sum_le_sum hpoint

theorem matrixCut_small_side {V : Type*} [Fintype V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1)
    {d c δ s : ℝ} (hrow : ∀ x, d ≤ ((∑ y, M x y : ℕ) : ℝ))
    (hcol : ∀ y, d ≤ ((∑ x, M x y : ℕ) : ℝ))
    (hmargin : c ≤ d - s - 2 * δ * Fintype.card V)
    (S T : Finset V)
    (hlarge : (1 - 2 * δ) * Fintype.card V < (S.card : ℝ) + T.card)
    (hsmall : min (S.card : ℝ) T.card ≤ s) :
    c * min (S.card : ℝ) T.card ≤ (matrixCut M S T : ℝ) := by
  have hle (A B : Finset V) (N : V → V → ℕ)
      (hN : ∀ x y, N x y ≤ 1)
      (hdeg : ∀ x, d ≤ ((∑ y, N x y : ℕ) : ℝ))
      (hA : (A.card : ℝ) ≤ s)
      (hab : (1 - 2 * δ) * Fintype.card V < (A.card : ℝ) + B.card) :
      c * A.card ≤ (matrixCut N A B : ℝ) := by
    have hh := matrixCut_row_lower N hN A B (fun x _ => hdeg x)
    have hb : c ≤ d + B.card - Fintype.card V := by linarith
    have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ A.card by positivity)
    nlinarith
  rcases le_total (S.card : ℝ) T.card with h | h
  · rw [min_eq_left h] at *
    exact hle S T M hM hrow hsmall hlarge
  · rw [min_eq_right h] at *
    rw [matrixCut_transpose]
    exact hle T S (fun x y => M y x) (fun x y => hM y x) hcol hsmall (by linarith)

theorem matrixCut_upper_of_degrees {V : Type*} [Fintype V]
    (M : V → V → ℕ) {b : ℝ}
    (hrow : ∀ x, ((∑ y, M x y : ℕ) : ℝ) ≤ b)
    (hcol : ∀ y, ((∑ x, M x y : ℕ) : ℝ) ≤ b)
    (S T : Finset V) :
    (matrixCut M S T : ℝ) ≤ b * min (S.card : ℝ) T.card := by
  have hle (N : V → V → ℕ) (A B : Finset V)
      (h : ∀ x, ((∑ y, N x y : ℕ) : ℝ) ≤ b) :
      (matrixCut N A B : ℝ) ≤ b * A.card := by
    have hh (x : V) : ((∑ y ∈ B, N x y : ℕ) : ℝ) ≤ b := by
      apply le_trans _ (h x)
      exact_mod_cast Finset.sum_le_univ_sum_of_nonneg (fun y => Nat.zero_le (N x y))
    have hs := Finset.sum_le_sum (fun x (_ : x ∈ A) => hh x)
    simpa only [matrixCut, Nat.cast_sum, Finset.sum_const, nsmul_eq_mul, mul_comm] using hs
  rcases le_total (S.card : ℝ) T.card with h | h
  · rw [min_eq_left h]; exact hle M S T hrow
  · rw [min_eq_right h, matrixCut_transpose]
    exact hle (fun x y => M y x) T S hcol

theorem matrixCut_loss_bound {V : Type*} [Fintype V]
    (M L W : V → V → ℕ) {b : ℝ}
    (hpoint : ∀ x y, M x y ≤ L x y + W x y)
    (hrow : ∀ x, ((∑ y, W x y : ℕ) : ℝ) ≤ b)
    (hcol : ∀ y, ((∑ x, W x y : ℕ) : ℝ) ≤ b)
    (S T : Finset V) :
    (matrixCut M S T : ℝ) - b * min (S.card : ℝ) T.card ≤ (matrixCut L S T : ℝ) := by
  have hh : matrixCut M S T ≤ matrixCut L S T + matrixCut W S T := by
    simp only [matrixCut, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hpoint x y))
  have hr : (matrixCut M S T : ℝ) ≤ (matrixCut L S T : ℝ) + matrixCut W S T := by exact_mod_cast hh
  linarith [matrixCut_upper_of_degrees W hrow hcol S T]

end Oberwolfach
