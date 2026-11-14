module

public import Oberwolfach.FiniteSignedAverages

@[expose] public section

/-! The all-pairs transfer formula corrects every zero-sum vector on a
finite set. Equal-index pairs contribute zero. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem balanced_pair_transfer_identity {I : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℝ) (hz : ∑ i,z i=0) (h : I) :
    (∑ i,∑ j,z i*((if h=i then (1:ℝ) else 0)-(if h=j then 1 else 0)))/(Fintype.card I:ℝ)=z h := by
  have hn : (0:ℝ)<Fintype.card I := by
    letI : Nonempty I := ⟨h⟩
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hi (i : I) :
      (∑ j,z i*((if h=i then (1:ℝ) else 0)-(if h=j then 1 else 0)))=
      (Fintype.card I:ℝ)*z i*(if h=i then 1 else 0)-z i := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,mul_one]
    ring
  simp only [hi,Finset.sum_sub_distrib,hz,sub_zero]
  have he : (∑ i,(Fintype.card I:ℝ)*z i*(if h=i then (1:ℝ) else 0))=
      (Fintype.card I:ℝ)*z h := by
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [he]
  field_simp

end Oberwolfach
