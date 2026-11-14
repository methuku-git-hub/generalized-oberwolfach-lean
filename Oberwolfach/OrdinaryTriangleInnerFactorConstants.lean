module

public import Oberwolfach.EndpointSourceCounts

@[expose] public section
/-! The inner triangle size margin and hub weight bounds are positive from
the original positive sampling and host constants. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_factor_constants
    (pmin κe c C:ℝ) (hp:0<pmin) (hκ:0<κe) (hc:0<c) (hC:0<C):
    0<min (pmin^4/32) (endpointCountCoefficient pmin κe/4) ∧
    0<c ∧ 0<4*C/pmin^7:=by
  have hcoeff:=endpointCountCoefficient_pos pmin κe hp hκ
  exact ⟨by positivity,hc,by positivity⟩
end Oberwolfach
