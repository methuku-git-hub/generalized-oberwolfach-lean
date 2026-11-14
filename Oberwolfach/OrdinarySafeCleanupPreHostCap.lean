module

public import Oberwolfach.OrdinarySafeCleanupScale

@[expose] public section
/-! The pre-host cap below one is the cap used by the packing rule. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_safe_cleanup_pre_host_cap
    (r:ℕ) (p βe βh ν cap:ℝ) (hcap:cap≤1):
    ordinarySafeCleanupScale r p βe βh ν (min cap 1)=ordinarySafeCleanupScale r p βe βh ν cap:=by
  rw [min_eq_left hcap]
end Oberwolfach
