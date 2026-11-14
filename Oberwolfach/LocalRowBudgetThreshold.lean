module

public import Oberwolfach.LocalRowFamilyErrorBudget

@[expose] public section
/-! The local-row threshold is chosen before the host and its size. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def localRowBudgetThreshold (C δ:ℝ) (hC:0≤C) (hδ:0<δ) : ℕ :=
  Classical.choose (local_row_distinct_scales_error_budget C δ hC hδ)

theorem localRowBudgetThreshold_spec (C δ:ℝ) (hC:0≤C) (hδ:0<δ) :
    1≤localRowBudgetThreshold C δ hC hδ ∧ ∀(I:Type) (T:Finset I) (a b:I→ℕ),
      (∀i∈T,localRowBudgetThreshold C δ hC hδ≤a i) → Set.InjOn a T →
      (∀i∈T,(b i:ℝ)≤C*(a i:ℝ)) →
      (∑i∈T,2*(b i:ℝ)*Real.exp (-2*(a i:ℝ)^(1/2:ℝ)))≤δ :=
  Classical.choose_spec (local_row_distinct_scales_error_budget C δ hC hδ)
end Oberwolfach
