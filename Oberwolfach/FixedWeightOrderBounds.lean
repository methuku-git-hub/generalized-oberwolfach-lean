module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Explicit conversion between the original and retained vertex orders.
The coefficient itself is not rescaled. -/
set_option autoImplicit false
namespace Oberwolfach

theorem fixed_weight_order_bounds (n a A B w:ℝ) (m:ℕ)
    (ha:0<a) (han:a≤n) (hna:n≤2*a) (hA:0≤A) (hB:0≤B)
    (hw:A/n^m≤w∧w≤B/n^m):
    (A/2^m)/a^m≤w∧w≤B/a^m:=by
  constructor
  · have hn:0<n:=ha.trans_le han
    have hh:=div_le_div_of_nonneg_left hA (pow_pos hn m)
      (pow_le_pow_left₀ (le_of_lt hn) hna m)
    rw [mul_pow,←div_div] at hh
    exact hh.trans hw.1
  · exact hw.2.trans (div_le_div_of_nonneg_left hB (pow_pos ha m)
      (pow_le_pow_left₀ ha.le han m))

end Oberwolfach
