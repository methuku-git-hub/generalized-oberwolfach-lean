module

public import Mathlib.Tactic

@[expose] public section
/-! Combine the per-state concentration estimates without changing their
parameters or assuming independence after the sample is fixed. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampled_class_degree_sum_bound
    {A:Type} [Fintype A] (T:Finset A) (f g:A→ℝ) (t:ℝ)
    (h:∀a∈T,|f a-g a|≤t):
    |(∑a∈T,f a)-(∑a∈T,g a)|≤T.card*t:=by
  rw [←Finset.sum_sub_distrib]
  calc
    |∑a∈T,(f a-g a)|≤∑a∈T,|f a-g a|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑_a∈T,t:=Finset.sum_le_sum h
    _=T.card*t:=by simp
end Oberwolfach
