module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section
/-! Fixed marked and ordinary root targets summing to one yield a near-unit
combined load, without replacing the supplied coefficients. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem finite_combined_unit_load {I:Type} [Fintype I]
    (target actual:I→ℝ) (τ t:ℝ) (hsum:∑i,target i=1)
    (h:∀i,|actual i-target i|≤t+τ*target i):
    |(∑i,actual i)-1|≤(Fintype.card I:ℝ)*t+τ:=by
  have hh:|(∑i,actual i)-(∑i,target i)|≤∑i,|actual i-target i|:=by
    rw [←Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hu:(∑i,|actual i-target i|)≤∑i,(t+τ*target i):=Finset.sum_le_sum (fun i _=>h i)
  have he:(∑i,(t+τ*target i))=(Fintype.card I:ℝ)*t+τ:=by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,hsum,mul_one]
  rw [hsum] at hh
  linarith
end Oberwolfach
