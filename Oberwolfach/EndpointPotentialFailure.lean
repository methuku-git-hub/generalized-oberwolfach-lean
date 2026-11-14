module

public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! Numeric normalization of endpoint pattern concentration on fixed domains. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach

theorem endpoint_row_variance_bound (a b K ω p C S:ℝ)
    (ha:0<a) (hω:0<ω) (hp:0<p) (hC:0<C) (hS:0<S)
    (hb:ω*a≤b) (hb':b≤K*a):
    let M:=C/(a*b*p^5)
    S^2*((M*(2*b+a))*5*(M*(b*a)))≤
      (S^2*5*(C/(ω*p^5))^2*(2*K+1)*K)/a:=by
  dsimp only
  have hb0:0<b:=(mul_pos hω ha).trans_le hb
  have hK:0<K:=by nlinarith only [hb0,hb',ha]
  have hm:C/(a*b*p^5)≤(C/(ω*p^5))/a^2:=by
    calc
      _≤C/(a*(ω*a)*p^5):=div_le_div_of_nonneg_left hC.le (by positivity) (by gcongr)
      _=_:=by field_simp <;> ring
  calc
    _≤S^2*((((C/(ω*p^5))/a^2)*((2*K+1)*a))*5*
      (((C/(ω*p^5))/a^2)*(K*a^2))):=by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg S)
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul hm (by nlinarith only [hb']) (by positivity) (by positivity)
        · exact mul_le_mul hm (by nlinarith only [mul_le_mul_of_nonneg_right hb' ha.le]) (by positivity) (by positivity)
        · positivity
        · positivity
    _=_:=by field_simp <;> ring

theorem endpoint_tail_variance_mono (t v w:ℝ) (hv:0<v) (hvw:v≤w):
    2*Real.exp (-2*t^2/v)≤2*Real.exp (-2*t^2/w):=by
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul,neg_div] using
    neg_le_neg (div_le_div_of_nonneg_left (show 0≤2*t^2 by positivity) hv hvw)

end Oberwolfach
