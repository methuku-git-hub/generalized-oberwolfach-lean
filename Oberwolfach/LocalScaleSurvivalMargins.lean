module

public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section

/-! Conversion of normalized physical-survival tails to a fixed inner
order. The leading candidate coefficient is independent of the ambient
size ratio; only the exponential failure constant uses that ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Oberwolfach

theorem localScale_exponential_tail (a n : ℕ) (ha : 0<a) (han : a≤n)
    (K β D : ℝ) (hK : 0<K) (hβ : 0<β) (hD : 0<D) (hnK : (n:ℝ)≤K*a) (k : ℕ) :
    2*Real.exp (-2*(β*((a:ℝ)/n)^k)^2/(D/n))≤
      2*Real.exp (-(2*(β/K^k)^2/D)*a) := by
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hnR : (0:ℝ)<n := by exact_mod_cast ha.trans_le han
  have hanR : (a:ℝ)≤n := by exact_mod_cast han
  have hratio : 1/K≤(a:ℝ)/n := (div_le_div_iff₀ hK hnR).mpr (by simpa only [one_mul,mul_one,mul_comm] using hnK)
  have ht : β/K^k≤β*((a:ℝ)/n)^k := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio k) hβ.le
    simpa only [div_pow,one_pow,mul_one_div] using hh
  have hcmp : 2*(β/K^k)^2*(a:ℝ)/D≤2*(β*((a:ℝ)/n)^k)^2*n/D := by
    gcongr
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have he : -2*(β*((a:ℝ)/n)^k)^2/(D/n)=-(2*(β*((a:ℝ)/n)^k)^2*n/D) := by
    field_simp
  rw [he]
  exact (neg_le_neg hcmp).trans (le_of_eq (by ring))

end Oberwolfach
