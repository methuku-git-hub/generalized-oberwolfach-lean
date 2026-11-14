module

public import Oberwolfach.FiniteBasisAverages

@[expose] public section

/-! Four signed injective families, averaged on one and the same domain. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def averagedBasisRectangle {I W : Type*} [Fintype I]
    (f₀₀ f₁₀ f₁₁ f₀₁ : I → W) (w : W) : ℝ :=
  averagedBasisDifference f₀₀ f₁₀ w-averagedBasisDifference f₀₁ f₁₁ w

theorem averagedBasisRectangle_test {I W : Type*} [Fintype I] [Fintype W]
    (f₀₀ f₁₀ f₁₁ f₀₁ : I → W) (t : W → ℝ) :
    (∑ w,averagedBasisRectangle f₀₀ f₁₀ f₁₁ f₀₁ w*t w)=
      (∑ i,(t (f₀₀ i)-t (f₁₀ i)+t (f₁₁ i)-t (f₀₁ i)))/(Fintype.card I:ℝ) := by
  unfold averagedBasisRectangle
  simp only [sub_mul,Finset.sum_sub_distrib,averagedBasisDifference_test]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  ring

theorem averagedBasisRectangle_bound {I W : Type*} [Fintype I]
    (f₀₀ f₁₀ f₁₁ f₀₁ : I ↪ W) (w : W) :
    |averagedBasisRectangle f₀₀ f₁₀ f₁₁ f₀₁ w|≤4/(Fintype.card I:ℝ) := by
  unfold averagedBasisRectangle
  have hh := abs_sub_le (averagedBasisDifference f₀₀ f₁₀ w) 0 (averagedBasisDifference f₀₁ f₁₁ w)
  simp only [sub_zero,zero_sub,abs_neg] at hh
  have h1 := averagedBasisDifference_bound f₀₀ f₁₀ w
  have h2 := averagedBasisDifference_bound f₀₁ f₁₁ w
  calc
    _ ≤ 2/(Fintype.card I:ℝ)+2/(Fintype.card I:ℝ) := hh.trans (add_le_add h1 h2)
    _ = _ := by ring

theorem averagedBasisRectangle_zero {I W : Type*} [Fintype I]
    (f₀₀ f₁₀ f₁₁ f₀₁ : I → W) (w : W)
    (h₀₀ : ∀ i,w≠f₀₀ i) (h₁₀ : ∀ i,w≠f₁₀ i)
    (h₁₁ : ∀ i,w≠f₁₁ i) (h₀₁ : ∀ i,w≠f₀₁ i) :
    averagedBasisRectangle f₀₀ f₁₀ f₁₁ f₀₁ w=0 := by
  unfold averagedBasisRectangle
  rw [averagedBasisDifference_zero _ _ _ h₀₀ h₁₀,averagedBasisDifference_zero _ _ _ h₀₁ h₁₁,sub_self]

end Oberwolfach
