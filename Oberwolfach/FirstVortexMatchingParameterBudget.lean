module

public import Oberwolfach.FirstVortexMatchingErrorBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_parameter_budget
    (n A:ℕ) (ε δ lam a γ:ℝ)
    (hδ:0≤δ) (hA:ε*n/2≤A)
    (ha:a≤lam/10) (hγ:γ≤lam/10) (hlam:8*lam≤5*δ*ε):
    2*(max a γ*n)≤δ*A/4:=by
  have hmax:max a γ≤lam/10:=max_le ha hγ
  apply first_vortex_matching_error_budget n A ε δ a γ hδ hA
  nlinarith only [hmax,hlam]
end Oberwolfach
