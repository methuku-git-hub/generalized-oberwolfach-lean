module

public import Oberwolfach.LongReservedListUniformNumericBudgets

@[expose] public section
/-! Quantify the scope of the old inverse-length hypothesis. This is a
diagnostic for the staged route, not an assumption of the main theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_old_trim_requires_very_large_length
    (r:ℕ) (α ρ₀:ℝ) (hα:0≤α) (hρ:0≤ρ₀) (hρ1:ρ₀≤1)
    (htrim:1/(100*((r+4:ℕ):ℝ))≤
      ((min (2*α) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16):
    40960000≤r+4:=by
  have hm0:0≤min (2*α) (1/4:ℝ):=le_min (by linarith) (by norm_num)
  have hm1:min (2*α) (1/4:ℝ)≤1/4:=min_le_right _ _
  have hsq:(ρ₀/200)^2≤(1/200:ℝ)^2:=by
    have hh:=mul_nonneg (sub_nonneg.mpr hρ1) (show (0:ℝ)≤1+ρ₀ by linarith)
    nlinarith
  have hprod:=mul_le_mul hm1 hsq (sq_nonneg (ρ₀/200)) (by norm_num : (0:ℝ)≤1/4)
  have hupper:((min (2*α) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16≤1/4096000000:=by
    nlinarith only [hprod]
  have hden:0<100*((r+4:ℕ):ℝ):=by positivity
  have hh:1≤(1/4096000000:ℝ)*(100*((r+4:ℕ):ℝ)):=
    (div_le_iff₀ hden).mp (htrim.trans hupper)
  have hr:(40960000:ℝ)≤((r+4:ℕ):ℝ):=by nlinarith only [hh]
  exact_mod_cast hr
end Oberwolfach
