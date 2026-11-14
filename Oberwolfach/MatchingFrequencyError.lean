module

public import Mathlib.Tactic

@[expose] public section
/-! Conversion of an r-fold hub count estimate to the prescribed frequency. -/
set_option autoImplicit false
namespace Oberwolfach

theorem matching_frequency_error
    (r actual η s n θ f error γ:ℝ) (hr:0<r)
    (hbalance:η*s=(1-θ)*f)
    (h:|r*actual-η*s*n|≤error+γ*(|η*s*n|+error)):
    |actual-(1-θ)*f*n/r|≤(error+γ*(|(1-θ)*f*n|+error))/r :=by
  have hr0:r≠0:=ne_of_gt hr
  have htarget:η*s*n=(1-θ)*f*n:=by rw [hbalance]
  rw [htarget] at h
  have heq:actual-(1-θ)*f*n/r=(r*actual-(1-θ)*f*n)/r:=by field_simp <;> ring
  rw [heq,abs_div,abs_of_pos hr]
  exact div_le_div_of_nonneg_right h hr.le
end Oberwolfach
