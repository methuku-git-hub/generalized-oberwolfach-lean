module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! The inner-domain scale used by the triangle fresh factors is positive
under the original lower bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_scale_coefficient_pos
    (pmin κe:ℝ) (hpmin:0<pmin) (hκe:0<κe):
    0<(min (pmin^4/32) (endpointCountCoefficient pmin κe/4))/4 :=by
  have h:=endpointCountCoefficient_pos pmin κe hpmin hκe
  positivity
end Oberwolfach
