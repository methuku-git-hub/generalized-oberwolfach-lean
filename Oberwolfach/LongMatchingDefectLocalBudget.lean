module

public import Oberwolfach.LongMatchingDefectSpacingBound

@[expose] public section
/-! The matching incidence defect fits the first-active local budget when
spacing is chosen after the first-vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_matching_defect_local_budget
    (K d n:ℕ) (θ lam epsOrd cap ε:ℝ) (hlam:lam≤1) (hd:0<d)
    (hspacing:1/(d:ℝ)≤cap*ε/16):
    let alphaOrd:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let gammaOrd:=min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    max alphaOrd gammaOrd*n≤cap*(ε*n)/128 :=by
  intro alphaOrd gammaOrd
  have hh:=long_matching_defect_spacing_bound K d θ lam epsOrd hlam hd
  have hcoeff:max alphaOrd gammaOrd≤cap*ε/128:=by
    have hnon:(0:ℝ)≤1/(d:ℝ):=by positivity
    have heq:1/(10*(d:ℝ))=(1/(d:ℝ))/10:=by ring
    rw [heq] at hh
    nlinarith only [hh,hspacing,hnon]
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg n
  have h:=mul_le_mul_of_nonneg_right hcoeff hn
  nlinarith only [h]
end Oberwolfach
