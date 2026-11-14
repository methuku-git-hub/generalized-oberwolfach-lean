module

public import Oberwolfach.LongManuscriptMatchingParameters

@[expose] public section
/-! The previous auxiliary tolerance choice forces spacing too large for a
cutoff-scale reserved block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem long_previous_spacing_exceeds_cutoff
    (K d:ℕ) (hK:3≤K) (hd:2≤d) (θ lam eps:ℝ)
    (hθ:0<θ) (hθmax:θ≤1/100) (hlam:0<lam) (hlamθ:lam≤θ)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hγ:min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))≤eps):
    K+1<d:=by
  have hKR:(3:ℝ)≤K:=by exact_mod_cast hK
  have hdR:(2:ℝ)≤d:=by exact_mod_cast hd
  have hKpos:(0:ℝ)<K:=by linarith
  have hdpos:(0:ℝ)<d:=by linarith
  have hden:(0:ℝ)<100*(K:ℝ)^2:=by positivity
  have hfrac:θ/(100*(K:ℝ)^2)≤1:=by
    apply (div_le_one hden).2
    nlinarith [sq_nonneg ((K:ℝ)-3)]
  have hsmall:eps<1/2:=by
    have hh:=mul_le_mul_of_nonneg_left hfrac hlam.le
    nlinarith
  have hdivle:lam/(10*(d:ℝ))≤lam/10:=by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<10*(d:ℝ)) (by norm_num : (0:ℝ)<10)).2
    nlinarith
  have hdiv:lam/(10*(d:ℝ))≤eps:=by
    by_contra! hn
    have hh:eps<min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)):=
      lt_min hsmall (lt_min hn (lt_of_lt_of_le hn hdivle))
    linarith
  have hdivBound:lam/(10*(d:ℝ))≤lam*(θ/(100*(K:ℝ)^2))/3:=by linarith
  have hineq:(30*(K:ℝ)^2)*lam≤(θ*(d:ℝ))*lam:=by
    have hh:=hdivBound
    field_simp at hh
    nlinarith
  have hineq':30*(K:ℝ)^2≤θ*(d:ℝ):=(mul_le_mul_iff_right₀ hlam).1 (by simpa only [mul_comm] using hineq)
  have hthetaD:θ*(d:ℝ)≤d:=by nlinarith
  have hKsq:(K:ℝ)≤(K:ℝ)^2:=by nlinarith
  have hresult:(K:ℝ)+1<(d:ℝ):=by nlinarith
  exact_mod_cast hresult
end Oberwolfach
