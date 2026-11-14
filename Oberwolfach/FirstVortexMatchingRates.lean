module

public import Oberwolfach.FirstVortexMatchingParameterBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_rates_le_lambda
    (d K:ℕ) (lam θ eps a γ:ℝ)
    (hd:1≤d) (hK:1≤K) (hlam:0≤lam) (hθ:0≤θ) (hθ1:θ≤1)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (ha:a≤lam/(10*(d:ℝ))) (hγ:γ≤eps/2):
    a≤lam/10 ∧ γ≤lam/10:=by
  have hdR:(1:ℝ)≤d:=by exact_mod_cast hd
  have hKR:(1:ℝ)≤K:=by exact_mod_cast hK
  have hK2:(1:ℝ)≤(K:ℝ)^2:=by nlinarith only [hKR]
  have hden:(0:ℝ)<100*(K:ℝ)^2:=by positivity
  have hfrac:θ/(100*(K:ℝ)^2)≤1/10:=by
    apply (div_le_iff₀ hden).2
    nlinarith only [hK2,hθ1]
  have hprod:=mul_le_mul_of_nonneg_left hfrac hlam
  have hleft:lam/(10*(d:ℝ))≤lam/10:=by
    apply (div_le_iff₀ (show (0:ℝ)<10*(d:ℝ) by positivity)).2
    nlinarith only [hlam,hdR,mul_nonneg hlam (sub_nonneg.mpr hdR)]
  constructor
  · exact ha.trans hleft
  · linarith only [hγ,heps,hprod,hlam]
end Oberwolfach
