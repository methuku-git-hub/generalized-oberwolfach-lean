module

public import Oberwolfach.PrescribedBoundaryMatchingLoadBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_error_budget
    (n A:ℕ) (ε δ a γ:ℝ)
    (hδ:0≤δ) (hA:ε*n/2≤A) (hscale:16*max a γ≤δ*ε):
    2*(max a γ*n)≤δ*A/4:=by
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg n
  have h₁:=mul_le_mul_of_nonneg_right hscale hn
  have h₂:=mul_le_mul_of_nonneg_left hA hδ
  nlinarith only [h₁,h₂]
end Oberwolfach
