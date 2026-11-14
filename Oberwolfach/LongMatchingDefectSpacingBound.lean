module

public import Oberwolfach.LongSelectorMatchingRatesBound

@[expose] public section
/-! The matching incidence defect can be made small independently of the
first-vortex scale by choosing the spacing sufficiently large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_matching_defect_spacing_bound
    (K d:ℕ) (θ lam epsOrd:ℝ) (hlam:lam≤1) (hd:0<d):
    let alphaOrd:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let gammaOrd:=min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    max alphaOrd gammaOrd≤1/(10*(d:ℝ)) :=by
  intro alphaOrd gammaOrd
  have hquot:lam/(10*(d:ℝ))≤1/(10*(d:ℝ)):=div_le_div_of_nonneg_right hlam (by positivity)
  apply max_le
  · exact (min_le_left _ _).trans hquot
  · exact ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))).trans hquot
end Oberwolfach
