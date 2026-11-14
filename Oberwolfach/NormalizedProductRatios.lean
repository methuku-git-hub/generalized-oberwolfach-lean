module

public import Oberwolfach.FiniteProductPerturbation

@[expose] public section

/-! Relative error for a quotient of falling-factorial correction
products. The population loss is summed before taking the reciprocal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_product_deficit {J : Type*} (S : Finset J) (x : J → ℝ)
    (hx : ∀ j∈S,0 ≤ x j ∧ x j ≤ 1) :
    0 ≤ 1-(∏ j∈S,(1-x j)) ∧ 1-(∏ j∈S,(1-x j)) ≤ ∑ j∈S,x j := by
  have hh := finite_product_perturbation S (fun _ => (1:ℝ)) (fun j => 1-x j)
    (fun j hj => ⟨by linarith [(hx j hj).2],by linarith [(hx j hj).1],le_rfl⟩)
  simpa only [Finset.prod_const_one,sub_sub_cancel] using hh

theorem normalized_product_ratio_error {J : Type*} (S : Finset J) (x y : J → ℝ)
    (hx : ∀ j∈S,0 ≤ x j ∧ x j ≤ 1) (hy : ∀ j∈S,0 ≤ y j ∧ y j ≤ 1)
    (hsmall : (∑ j∈S,y j) ≤ 1/2) :
    |(∏ j∈S,(1-x j))/(∏ j∈S,(1-y j))-1| ≤ 2*((∑ j∈S,x j)+(∑ j∈S,y j)) := by
  have h₁ := finite_product_deficit S x hx
  have h₂ := finite_product_deficit S y hy
  have hB : (0:ℝ)<∏ j∈S,(1-y j) := by linarith
  have hdiff : |(∏ j∈S,(1-x j))-(∏ j∈S,(1-y j))| ≤
      (∑ j∈S,x j)+(∑ j∈S,y j) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hsum : 0 ≤ (∑ j∈S,x j)+(∑ j∈S,y j) :=
    add_nonneg (Finset.sum_nonneg (fun j hj => (hx j hj).1))
      (Finset.sum_nonneg (fun j hj => (hy j hj).1))
  have he : (∏ j∈S,(1-x j))/(∏ j∈S,(1-y j))-1=
      ((∏ j∈S,(1-x j))-(∏ j∈S,(1-y j)))/(∏ j∈S,(1-y j)) := by field_simp
  rw [he,abs_div,abs_of_pos hB]
  apply (div_le_iff₀ hB).mpr
  nlinarith

end Oberwolfach
