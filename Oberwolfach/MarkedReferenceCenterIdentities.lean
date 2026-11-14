module

public import Oberwolfach.MarkedReferenceStatistics

@[expose] public section
/-! The common rim and spoke centers agree for the original density
parameters and every number of hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_reference_center_identities (rho t U:ℝ) (m:ℕ) (hρ:rho≠0):
    (rho*((m:ℝ)*t)/2)*(2*U/rho)=(m:ℝ)*(t*U) ∧
    (rho*t/2)*(2*U/rho)=t*U:=by
  constructor <;> field_simp <;> ring
end Oberwolfach
