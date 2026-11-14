module

public import Oberwolfach.ReservedCapacitySufficient

@[expose] public section
/-! The manuscript's n^(1/4) cutoff implies its displayed error bound,
expressed here using x = n^(1/4). -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reserved_root_error_bound
    (x c d theta : ℝ) (hx : 0 < x) (hc : 0 < c) (hd : 0 < d)
    (hθ : 0 < theta) (hlarge : 8*c/theta < x) :
    2*x^3/d < theta*x^4/(4*(c*d)) := by
  have hs : 8*c < theta*x := by
    have hh := (div_lt_iff₀ hθ).mp hlarge
    nlinarith
  have hp := mul_lt_mul_of_pos_right hs (pow_pos hx 3)
  apply (div_lt_div_iff₀ hd (by positivity : 0 < 4*(c*d))).2
  nlinarith [hp]
end Oberwolfach
