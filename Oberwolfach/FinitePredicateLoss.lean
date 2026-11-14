module

public import Mathlib.Tactic

@[expose] public section

/-! Removing terms with fixed coefficients: the loss is measured on the
realised removed index set, without a probability multiplier. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_predicate_loss {I:Type*} [Fintype I] (P Q:I→Prop) (w:I→ℝ) (M:ℝ)
    (hQP:∀ i,Q i→P i) (hw:∀ i,P i→0≤w i∧w i≤M) :
    0≤(∑ i,if P i then w i else 0)-(∑ i,if Q i then w i else 0) ∧
    (∑ i,if P i then w i else 0)-(∑ i,if Q i then w i else 0)≤
      M*(Finset.univ.filter (fun i=>P i∧¬Q i)).card := by
  have he:(∑ i,if P i then w i else 0)-(∑ i,if Q i then w i else 0)=
      ∑ i∈Finset.univ.filter (fun i=>P i∧¬Q i),w i:=by
    rw [←Finset.sum_sub_distrib,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hQ:Q i
    · simp [hQ,hQP i hQ]
    · by_cases hP:P i <;> simp [hP,hQ]
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun i hi=>(hw i (Finset.mem_filter.mp hi).2.1).1)
  · calc
      _ ≤ ∑ i∈Finset.univ.filter (fun i=>P i∧¬Q i),M:=
        Finset.sum_le_sum (fun i hi=>(hw i (Finset.mem_filter.mp hi).2.1).2)
      _ = _:=by simp [mul_comm]

end Oberwolfach
