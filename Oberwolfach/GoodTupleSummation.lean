module

public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! Summing a uniform approximation over tuples. Tuples declared bad have
zero contribution; their lost main terms are counted explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_sum_good_approximation {X : Type*} [Fintype X]
    (P : X → Prop) (f : X → ℝ) {b ε : ℝ} (hb : 0≤b) (hε : 0≤ε)
    (hgood : ∀ x,¬P x → b≤f x ∧ f x≤(1+ε)*b)
    (hbad : ∀ x,P x → f x=0) :
    |(∑ x,f x)-(Fintype.card X : ℝ)*b|≤
      (Fintype.card X : ℝ)*ε*b+
        ((Finset.univ.filter P).card : ℝ)*b := by
  classical
  have hpoint (x : X) : |f x-b|≤ε*b+(if P x then b else 0) := by
    by_cases hx : P x
    · rw [hbad x hx,if_pos hx,zero_sub,abs_neg,abs_of_nonneg hb]
      nlinarith
    · rw [if_neg hx,add_zero,abs_of_nonneg (sub_nonneg.mpr (hgood x hx).1)]
      linarith [(hgood x hx).2]
  calc
    _ = |∑ x,(f x-b)| := by rw [Finset.sum_sub_distrib];simp
    _ ≤ ∑ x,|f x-b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x,(ε*b+(if P x then b else 0)) := Finset.sum_le_sum (fun x _=>hpoint x)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have he : (∑ x,if P x then b else 0)=((Finset.univ.filter P).card : ℝ)*b := by
        rw [← Finset.sum_filter]
        simp
      rw [he]
      ring

end Oberwolfach
