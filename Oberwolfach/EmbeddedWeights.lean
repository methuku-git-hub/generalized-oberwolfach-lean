module

public import Oberwolfach.IntervalPathWeights

@[expose] public section

/-! Extension of weights along an injective representation map. There is
no multiplicity factor, and every incidence sum has an exact pullback. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def embeddedWeight {A B : Type*} [Fintype A]
    (f : A ↪ B) (w : A → ℝ) (b : B) : ℝ := ∑ a, if f a = b then w a else 0

theorem embeddedWeight_apply {A B : Type*} [Fintype A]
    (f : A ↪ B) (w : A → ℝ) (a : A) : embeddedWeight f w (f a) = w a := by
  unfold embeddedWeight
  simp only [f.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem embeddedWeight_not_in_range {A B : Type*} [Fintype A]
    (f : A ↪ B) (w : A → ℝ) (b : B) (hb : b ∉ Set.range f) : embeddedWeight f w b = 0 := by
  unfold embeddedWeight
  apply Finset.sum_eq_zero
  intro a _
  exact if_neg (fun h => hb ⟨a,h⟩)

theorem embeddedWeight_nonneg {A B : Type*} [Fintype A]
    (f : A ↪ B) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (b : B) : 0 ≤ embeddedWeight f w b := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hw a
  · exact le_refl _

theorem embeddedWeight_bound {A B : Type*} [Fintype A]
    (f : A ↪ B) (w : A → ℝ) (C : ℝ) (hC : 0 ≤ C) (hw : ∀ a, w a ≤ C) (b : B) :
    embeddedWeight f w b ≤ C := by
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hb
    rw [embeddedWeight_apply]
    exact hw a
  · rw [embeddedWeight_not_in_range f w b hb]
    exact hC

theorem embeddedWeight_incidence {A B : Type*} [Fintype A] [Fintype B]
    (f : A ↪ B) (w : A → ℝ) (E : B → Prop) :
    (∑ b, if E b then embeddedWeight f w b else 0) = ∑ a, if E (f a) then w a else 0 := by
  have h := finite_marginal_test w f (embeddedWeight f w) (fun _ => rfl)
    (fun b => if E b then (1 : ℝ) else 0)
  simpa only [mul_ite, mul_one, mul_zero] using h.symm

end Oberwolfach
