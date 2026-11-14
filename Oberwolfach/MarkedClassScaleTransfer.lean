module

public import Mathlib.Tactic

@[expose] public section

/-! Rescale fixed coefficients from ambient order n to the class size k.
The weights themselves are unchanged. -/
set_option autoImplicit false
namespace Oberwolfach
 theorem marked_class_weight_rescale (m:ℕ) (a n k lo hi w:ℝ)
    (ha:0<a) (hn:0<n) (hak:a*n≤k) (hkn:k≤n) (hlo:0≤lo) (hhi:0≤hi)
    (hw:lo/n^m≤w∧w≤hi/n^m):
    lo*a^m/k^m≤w∧w≤hi/k^m:=by
  have hk:0<k:=lt_of_lt_of_le (mul_pos ha hn) hak
  have hnk:n^m≤(k/a)^m:=pow_le_pow_left₀ hn.le ((le_div_iff₀ ha).mpr (by nlinarith only [hak])) m
  have hakpow:(a*n)^m≤k^m:=pow_le_pow_left₀ (by positivity) hak m
  have hknpow:k^m≤n^m:=pow_le_pow_left₀ hk.le hkn m
  constructor
  · apply le_trans _ hw.1
    apply (div_le_div_iff₀ (pow_pos hk m) (pow_pos hn m)).mpr
    have hh:=mul_le_mul_of_nonneg_left hakpow hlo
    rw [mul_pow] at hh
    nlinarith only [hh]
  · apply hw.2.trans
    exact div_le_div_of_nonneg_left hhi (pow_pos hk m) hknpow

 theorem marked_class_count_rescale (r:ℕ) (a n k count:ℝ)
    (ha:0≤a) (hk:0≤k) (hkn:k≤n) (hcount:a*n^r≤count):a*k^r≤count:=
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk hkn r) ha).trans hcount
end Oberwolfach
