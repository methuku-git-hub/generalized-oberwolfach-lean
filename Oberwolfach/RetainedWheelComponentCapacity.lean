module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! The matching's relative count estimate leaves strictly fewer wheels
than available components whenever the error is smaller than the slack. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem retained_wheel_component_capacity
    (r count available:ℕ) (f n θ lam:ℝ)
    (hr:0<r) (hf:0<f) (hn:0<n) (hlam:lam<θ)
    (hbound:((r:ℝ)*count) ≤ (1-θ+lam)*f*n)
    (havailable:f*n≤(r:ℝ)*available):
    count<available :=by
  have hslack:0<(θ-lam)*f*n:=mul_pos (mul_pos (sub_pos.mpr hlam) hf) hn
  have hlt:(r:ℝ)*count<(r:ℝ)*available:=by nlinarith
  have hr':0<(r:ℝ):=by exact_mod_cast hr
  have hc:(count:ℝ)<available:=lt_of_mul_lt_mul_left hlt (le_of_lt hr')
  exact_mod_cast hc
end Oberwolfach
