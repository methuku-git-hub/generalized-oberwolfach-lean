module

public import Mathlib.Tactic

@[expose] public section

/-! Explicit conversion of fixed inner-domain count and weight bounds to
ambient order. The coefficient function itself is not rescaled. -/
set_option autoImplicit false
namespace Oberwolfach

theorem inner_ambient_weight_scale (m:ℕ) (n a κ b B w:ℝ)
    (hn:0<n) (ha:0<a) (hk:0<κ) (hb:0≤b) (hB:0≤B)
    (han:a≤n) (hka:κ*n≤a) (hw:b/a^m≤w∧w≤B/a^m):
    b/n^m≤w∧w≤(B/κ^m)/n^m:=by
  constructor
  · exact (div_le_div_of_nonneg_left hb (pow_pos ha _) (pow_le_pow_left₀ ha.le han _)).trans hw.1
  · apply hw.2.trans
    rw [div_div,←mul_pow]
    exact div_le_div_of_nonneg_left hB (pow_pos (mul_pos hk hn) _) (pow_le_pow_left₀ (mul_nonneg hk.le hn.le) hka _)

theorem inner_ambient_count_scales (m:ℕ) (n a κ β:ℝ)
    (hn:0≤n) (ha:0≤a) (hk:0≤κ) (hk1:κ≤1) (hβ:0≤β) (hka:κ*n≤a):
    (β*κ^(m+1))*n^(m+1)≤β*a^(m+1)∧
    (β*κ^(m+1))*n^m≤β*a^m:=by
  have hm:κ^m*n^m≤a^m:=by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hk hn) hka m
  have hs:κ^(m+1)*n^(m+1)≤a^(m+1):=by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hk hn) hka (m+1)
  have hstep:κ^(m+1)≤κ^m:=by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_left hk1 (pow_nonneg hk m)).trans_eq (mul_one _)
  constructor
  · nlinarith only [mul_le_mul_of_nonneg_left hs hβ]
  · have h':=mul_le_mul_of_nonneg_right hstep (pow_nonneg hn m)
    nlinarith only [mul_le_mul_of_nonneg_left (h'.trans hm) hβ]

end Oberwolfach
