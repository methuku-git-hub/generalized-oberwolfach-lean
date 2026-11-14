module

public import Oberwolfach.FiniteSignedAverages
public import Oberwolfach.OrdinaryVertexTransfer

@[expose] public section

/-! Signed averages of two injective families of basis vectors. This records
the representation multiplicity used by common-cycle hub transfers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def averagedBasisDifference {I W : Type*} [Fintype I] (f g : I → W) (w : W) : ℝ :=
  finiteSignedAverage (fun i w => (if w=f i then (1:ℝ) else 0)-(if w=g i then 1 else 0)) w

theorem averagedBasisDifference_test {I W : Type*} [Fintype I] [Fintype W]
    (f g : I → W) (t : W → ℝ) :
    (∑ w,averagedBasisDifference f g w*t w)=
      (∑ i,(t (f i)-t (g i)))/(Fintype.card I:ℝ) := by
  unfold averagedBasisDifference
  rw [finiteSignedAverage_test]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [sub_mul,Finset.sum_sub_distrib]
  simp

theorem averagedBasisDifference_bound {I W : Type*} [Fintype I]
    (f g : I ↪ W) (w : W) :
    |averagedBasisDifference f g w|≤2/(Fintype.card I:ℝ) := by
  have hf : (∑ i,if w=f i then (1:ℝ) else 0)≤1 := by
    have hh := injective_range_indicator f w
    simp only [eq_comm] at hh
    rw [← hh]
    split_ifs <;> norm_num
  have hg : (∑ i,if w=g i then (1:ℝ) else 0)≤1 := by
    have hh := injective_range_indicator g w
    simp only [eq_comm] at hh
    rw [← hh]
    split_ifs <;> norm_num
  apply (finiteSignedAverage_abs_le _ _).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ i,((if w=f i then (1:ℝ) else 0)+(if w=g i then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> norm_num
    _ = (∑ i,if w=f i then (1:ℝ) else 0)+(∑ i,if w=g i then (1:ℝ) else 0) := Finset.sum_add_distrib
    _ ≤ 2 := by linarith

theorem averagedBasisDifference_zero {I W : Type*} [Fintype I]
    (f g : I → W) (w : W) (hf : ∀ i,w≠f i) (hg : ∀ i,w≠g i) :
    averagedBasisDifference f g w=0 := by
  apply finiteSignedAverage_eq_zero
  intro i
  simp only [hf i,hg i,ite_false,sub_self]

end Oberwolfach
