module

public import Oberwolfach.CloseSelectionCounts

@[expose] public section

/-! Explicit losses from discarding tuples with a close pair. One fixed
coordinate gives a constant loss; two separated fixed coordinates give
an inverse-order loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem permutation_close_weight_loss {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (A : Finset I) (a : I → V)
    (hA : 1 ≤ A.card) (hfree : A.card + 1 ≤ Fintype.card I)
    (hsep : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ PermutationClose π b (a i) (a j))
    (w : (I → V) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ f, w f ≤ C / (Fintype.card V : ℝ) ^ (Fintype.card I - 2)) :
    (∑ f : I → V, if (∀ i ∈ A, f i = a i) ∧
      (∃ i j, i ≠ j ∧ PermutationClose π b (f i) (f j)) then w f else 0) ≤
      (Fintype.card I : ℝ) ^ 2 * (2 * b + 1) * C /
        (Fintype.card V : ℝ) ^ (A.card - 1) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  let Bad (f : I → V) := (∀ i ∈ A, f i = a i) ∧
    ∃ i j, i ≠ j ∧ PermutationClose π b (f i) (f j)
  have hcount : (Fintype.card {f : I → V // Bad f} : ℝ) ≤
      (Fintype.card I : ℝ) ^ 2 * (2 * b + 1) *
        (Fintype.card V : ℝ) ^ (Fintype.card I - A.card - 1) := by
    exact_mod_cast permutation_close_selections_card π b A a hsep
  have hpower : (Fintype.card V : ℝ) ^ (Fintype.card I - 2) =
      (Fintype.card V : ℝ) ^ (Fintype.card I - A.card - 1) *
        (Fintype.card V : ℝ) ^ (A.card - 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ ∑ f : I → V, if Bad f then C / (Fintype.card V : ℝ) ^ (Fintype.card I - 2) else 0 := by
      apply Finset.sum_le_sum
      intro f _
      change (if Bad f then w f else 0) ≤ _
      split_ifs
      · exact hw f
      · exact le_refl _
    _ = (Fintype.card {f : I → V // Bad f} : ℝ) *
        (C / (Fintype.card V : ℝ) ^ (Fintype.card I - 2)) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
    _ ≤ ((Fintype.card I : ℝ) ^ 2 * (2 * b + 1) *
        (Fintype.card V : ℝ) ^ (Fintype.card I - A.card - 1)) *
        (C / (Fintype.card V : ℝ) ^ (Fintype.card I - 2)) :=
      mul_le_mul_of_nonneg_right hcount (div_nonneg hC (by positivity))
    _ = _ := by rw [hpower]; field_simp

end Oberwolfach
