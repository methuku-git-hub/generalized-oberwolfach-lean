module

public import Oberwolfach.DirectedCutBounds

@[expose] public section

/-! Large cuts in a bipartite adjacency matrix with degree above half the
part size. The two copies of the label set are kept as separate sides. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem matrixCut_large_of_minDegree {V : Type*} [Fintype V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1) (β δ : ℝ)
    (hrow : ∀ x, (1 / 2 + β) * Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ))
    (hcol : ∀ y, (1 / 2 + β) * Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ))
    (S T : Finset V)
    (hlarge : (1 - 2 * δ) * Fintype.card V < (S.card : ℝ) + T.card) :
    (β - δ) * Fintype.card V * min (S.card : ℝ) T.card ≤ (matrixCut M S T : ℝ) := by
  have hsmallLarge (A B : Finset V) (N : V → V → ℕ)
      (hN : ∀ x y, N x y ≤ 1)
      (hdeg : ∀ x, (1 / 2 + β) * Fintype.card V ≤ ((∑ y, N x y : ℕ) : ℝ))
      (hab : (A.card : ℝ) ≤ B.card)
      (hlarge : (1 - 2 * δ) * Fintype.card V < (A.card : ℝ) + B.card) :
      (β - δ) * Fintype.card V * A.card ≤ (matrixCut N A B : ℝ) := by
    have hb : (1 / 2 - δ) * Fintype.card V ≤ (B.card : ℝ) := by linarith
    have hh := matrixCut_row_lower N hN A B (fun x _ => hdeg x)
    have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ A.card by positivity)
    nlinarith
  rcases le_total (S.card : ℝ) T.card with h | h
  · rw [min_eq_left h]
    exact hsmallLarge S T M hM hrow h hlarge
  · rw [min_eq_right h, matrixCut_transpose]
    exact hsmallLarge T S (fun x y => M y x) (fun x y => hM y x) hcol h (by linarith)

theorem matrixEdges_normalized_large_cuts {V : Type*} [Fintype V] [DecidableEq V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1) (β δ h : ℝ)
    (hn : 0 < Fintype.card V) (hh : h ≤ β - δ)
    (hrow : ∀ x, (1 / 2 + β) * Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ))
    (hcol : ∀ y, (1 / 2 + β) * Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ))
    (S T : Finset V)
    (hlarge : 1 - 2 * δ < (S.card : ℝ) / Fintype.card V + (T.card : ℝ) / Fintype.card V) :
    h * Fintype.card V * Fintype.card V *
      min ((S.card : ℝ) / Fintype.card V) ((T.card : ℝ) / Fintype.card V) ≤
    ((Finset.univ.filter (fun e : BipartiteEdges M => e.1 ∈ S ∧ e.2.1 ∈ T)).card : ℝ) := by
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hl : (1 - 2 * δ) * Fintype.card V < (S.card : ℝ) + T.card := by
    rw [← add_div] at hlarge
    exact (lt_div_iff₀ hn').mp hlarge
  have hcut := matrixCut_large_of_minDegree M hM β δ hrow hcol S T hl
  have hm0 : 0 ≤ min (S.card : ℝ) T.card := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcut' : h * Fintype.card V * min (S.card : ℝ) T.card ≤ (matrixCut M S T : ℝ) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hn'.le) hm0).trans hcut
  rw [min_div_div_right hn'.le]
  have hcancel : h * Fintype.card V * Fintype.card V *
      (min (S.card : ℝ) T.card / Fintype.card V) =
      h * Fintype.card V * min (S.card : ℝ) T.card := by field_simp
  rw [hcancel, bipartiteEdges_filter_card M (fun x y => x ∈ S ∧ y ∈ T)]
  convert hcut' using 1
  simp only [matrixCut]
  congr 1
  calc
    _ = ∑ x : V, if x ∈ S then ∑ y ∈ T, M x y else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S
      · simp [hx, ← Finset.sum_filter]
      · simp [hx]
    _ = _ := by rw [← Finset.sum_filter]; simp

end Oberwolfach
