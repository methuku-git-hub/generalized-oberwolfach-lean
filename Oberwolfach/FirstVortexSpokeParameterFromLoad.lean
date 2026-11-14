module

public import Oberwolfach.LongResidualSpokeControlFromSmallImages

@[expose] public section
/-! The squared load is a valid separate spoke-control parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_spoke_parameter_from_load (load:ℝ) (hload:0≤load):
    0≤load^2 ∧ load≤Real.sqrt (load^2):=by
  refine ⟨sq_nonneg _,?_⟩
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hload]
end Oberwolfach
