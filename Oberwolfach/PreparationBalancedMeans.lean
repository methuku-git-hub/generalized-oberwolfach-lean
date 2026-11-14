module

public import Oberwolfach.ApproximatePreparationTargetArithmetic

@[expose] public section
/-! Positional errors combine without changing the fixed target coefficients. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_balanced_means {I:Type} [Fintype I] (τ a m:ℝ) (b z:I→ℝ)
    (hbalance:a+∑ i,b i=1) (hm:(1-τ)*a≤m ∧ m≤(1+τ)*a)
    (hz:∀ i,(1-τ)*b i≤z i ∧ z i≤(1+τ)*b i):
    1-τ≤m+∑ i,z i ∧ m+∑ i,z i≤1+τ:=by
  have hlo:∑ i,(1-τ)*b i≤∑ i,z i:=Finset.sum_le_sum (fun i _=>(hz i).1)
  have hhi:∑ i,z i≤∑ i,(1+τ)*b i:=Finset.sum_le_sum (fun i _=>(hz i).2)
  rw [←Finset.mul_sum] at hlo hhi
  constructor
  · nlinarith [hm.1,hbalance]
  · nlinarith [hm.2,hbalance]
end Oberwolfach
