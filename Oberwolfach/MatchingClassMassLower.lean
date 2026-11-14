module

public import Oberwolfach.OrdinaryAssignedMatchedRelativeFrequency

@[expose] public section
/-! Summing the retained class-frequency estimates gives a lower bound on
the total selected cycle mass. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem matching_class_mass_lower
    {I:Type} [Fintype I] [DecidableEq I]
    (T:Finset I) (len count:I→ℕ) (f:I→ℝ) (n θ err:ℝ)
    (hdev:∀i∈T,|((len i:ℝ)*(count i:ℝ))-(1-θ)*f i*n|≤err*f i*n):
    (1-θ-err)*n*(∑i∈T,f i)≤∑i:I,(len i:ℝ)*(count i:ℝ):=by
  have hp:∀i∈T,(1-θ-err)*n*f i≤(len i:ℝ)*(count i:ℝ):=by
    intro i hi
    have hh : -((err*f i*n))≤(len i:ℝ)*(count i:ℝ)-(1-θ)*f i*n:=(abs_le.mp (hdev i hi)).1
    nlinarith
  have hs:=Finset.sum_le_sum hp
  have hall:(∑i∈T,(len i:ℝ)*(count i:ℝ))≤∑i:I,(len i:ℝ)*(count i:ℝ):=by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    intro i hi hnot
    positivity
  have heq:(∑i∈T,(1-θ-err)*n*f i)=(1-θ-err)*n*(∑i∈T,f i):=by rw [Finset.mul_sum]
  rw [heq] at hs
  exact hs.trans hall
end Oberwolfach
