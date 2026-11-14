module

public import Oberwolfach.MatchingClassMassLower

@[expose] public section
/-! If only retained classes have selected wheels, their test estimates also
bound the total selected cycle mass from above. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem matching_class_mass_upper
    {I:Type} [Fintype I] [DecidableEq I]
    (T:Finset I) (len count:I→ℕ) (f:I→ℝ) (n θ err:ℝ)
    (hzero:∀i,i∉T→count i=0)
    (hdev:∀i∈T,|((len i:ℝ)*(count i:ℝ))-(1-θ)*f i*n|≤err*f i*n):
    (∑i:I,(len i:ℝ)*(count i:ℝ))≤(1-θ+err)*n*(∑i∈T,f i):=by
  have hp:∀i∈T,(len i:ℝ)*(count i:ℝ)≤(1-θ+err)*n*f i:=by
    intro i hi
    have hh:((len i:ℝ)*(count i:ℝ))-(1-θ)*f i*n≤err*f i*n:=(abs_le.mp (hdev i hi)).2
    nlinarith
  have hs:=Finset.sum_le_sum hp
  have heq:(∑i∈T,(1-θ+err)*n*f i)=(1-θ+err)*n*(∑i∈T,f i):=by rw [Finset.mul_sum]
  have hall:(∑i∈T,(len i:ℝ)*(count i:ℝ))=∑i:I,(len i:ℝ)*(count i:ℝ):=by
    apply Finset.sum_subset (Finset.subset_univ T)
    intro i _ hi
    rw [hzero i hi]
    simp
  rw [heq,hall] at hs
  exact hs
end Oberwolfach
