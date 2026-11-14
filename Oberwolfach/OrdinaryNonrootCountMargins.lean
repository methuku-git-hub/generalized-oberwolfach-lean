module

public import Oberwolfach.OrdinaryNonrootCountsLower

@[expose] public section
/-! A single explicit small-root inequality discharges the isolator and
transfer count margins for any positive integer exponent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_count_margin (n m t c β βfree:ℝ) (q:ℕ)
    (hn:0≤n) (hm:0≤m) (hmn:m≤n) (hβfree:0≤βfree) (hq:1≤q)
    (hsmall:c*t≤(β-βfree)*n):
    βfree*m^q+c*t*n^(q-1)≤β*n^q:=by
  have hp:m^q≤n^q:=pow_le_pow_left₀ hm hmn q
  have h1:=mul_le_mul_of_nonneg_left hp hβfree
  have h2:=mul_le_mul_of_nonneg_right hsmall (pow_nonneg hn (q-1))
  have he:n*n^(q-1)=n^q:=by
    have hq':q-1+1=q:=by omega
    calc
      n*n^(q-1)=n^(q-1+1):=by rw [pow_succ];ring
      _=n^q:=by rw [hq']
  calc
    _ ≤ βfree*n^q+(β-βfree)*n*n^(q-1):=add_le_add h1 h2
    _ = β*n^q:=by rw [mul_assoc,he];ring
end Oberwolfach
