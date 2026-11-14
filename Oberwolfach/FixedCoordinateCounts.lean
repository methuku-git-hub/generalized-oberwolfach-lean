module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

/-! Exact counts of vertex selections after specified coordinates are fixed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fixedCoordinatesEquiv {I X : Type*} [DecidableEq I]
    (A : Finset I) (a : I → X) :
    {f : I → X // ∀ i ∈ A, f i = a i} ≃ ({i : I // i ∉ A} → X) where
  toFun f i := f.val i.val
  invFun g := ⟨fun i => if hi : i ∈ A then a i else g ⟨i, hi⟩,
    by intro i hi; simp only [hi, dite_true]⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ A
    · simp only [hi, dite_true]
      exact (f.property i hi).symm
    · simp only [hi, dite_false]
  right_inv g := by
    funext i
    simp only [i.property, dite_false]

theorem fixedCoordinates_card {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]
    (A : Finset I) (a : I → X) :
    Fintype.card {f : I → X // ∀ i ∈ A, f i = a i} =
      Fintype.card X ^ (Fintype.card I - A.card) := by
  classical
  rw [Fintype.card_congr (fixedCoordinatesEquiv A a), Fintype.card_fun,
    Fintype.card_subtype_compl]
  congr 2
  exact Fintype.card_coe A

theorem fixedCoordinates_weight_bound {I X : Type*}
    [Fintype I] [Fintype X] [DecidableEq I]
    (A : Finset I) (a : I → X) (w : (I → X) → ℝ) (M : ℝ)
    (hw : ∀ f, w f ≤ M) :
    (∑ f : {f : I → X // ∀ i ∈ A, f i = a i}, w f.val) ≤
      (Fintype.card X : ℝ) ^ (Fintype.card I - A.card) * M := by
  classical
  calc
    _ ≤ ∑ _f : {f : I → X // ∀ i ∈ A, f i = a i}, M :=
      Finset.sum_le_sum (fun f _ => hw f.val)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, fixedCoordinates_card,
        Nat.cast_pow]

end Oberwolfach
