module

public import Oberwolfach.FirstVortexRetentionExactChoice

@[expose] public section
/-! The exact change tolerance inherits any upper bound chosen for the
original global cap, with the factor two recorded explicitly. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_exact_change_le_cap
    (ζChange cap bound:ℝ)
    (hExact:ζChange=(min cap (1:ℝ))/2) (hCap:cap≤2*bound):
    ζChange≤bound :=by
  have hmin:min cap (1:ℝ)≤cap:=min_le_left _ _
  linarith
end Oberwolfach
