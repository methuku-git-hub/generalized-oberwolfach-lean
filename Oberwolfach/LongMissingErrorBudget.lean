module

public import Oberwolfach.LongOrdinaryMassErrorBudget

@[expose] public section
/-! The original matching-error tolerances fit inside θ once spacing is
chosen at least as large as the fixed block size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_missing_error_le_theta
    (m d:ℕ) (hd:m+2≤d) (θ lam α γ:ℝ)
    (hθ:0≤θ) (hlam:0≤lam) (hlamθ:lam≤θ)
    (hα:α≤lam/(10*(d:ℝ))) (hγ:γ≤lam/(10*(d:ℝ))):
    ((m:ℝ)+2)*max α γ≤θ:=by
  have hd0:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hdm:(m:ℝ)+2≤d:=by exact_mod_cast hd
  have hmax:max α γ≤lam/(10*(d:ℝ)):=max_le hα hγ
  have hcap:0≤lam/(10*(d:ℝ)):=by positivity
  have hmul:=mul_le_mul_of_nonneg_left hmax (show 0≤(m:ℝ)+2 by positivity)
  have hmul2:=mul_le_mul_of_nonneg_right hdm hcap
  have heq:(d:ℝ)*(lam/(10*(d:ℝ)))=lam/10:=by field_simp
  rw [heq] at hmul2
  nlinarith
end Oberwolfach
