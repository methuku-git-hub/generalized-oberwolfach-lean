module

public import Oberwolfach.LongCorrectionStrictBudgetGivenInner

@[expose] public section
/-! The actual matching tolerances returned after spacing are bounded by that
spacing, so a cap selected earlier also controls the later matching loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_selector_matching_rates_bound
    (K d:ℕ) (θ lam epsOrd ζOrd:ℝ)
    (hK:3≤K) (hθ:0≤θ) (hθ1:θ≤1) (hlam:0≤lam) (hlamθ:lam≤θ)
    (heps:3*epsOrd≤lam*(θ/(100*(K:ℝ)^2))) (hζ:ζOrd≤epsOrd/8):
    let alphaOrd:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let gammaOrd:=min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    alphaOrd≤θ ∧ gammaOrd≤θ ∧ ζOrd≤θ :=by
  intro alphaOrd gammaOrd
  have hKreal:(3:ℝ)≤K:=by exact_mod_cast hK
  have hden:1≤100*(K:ℝ)^2:=by nlinarith [sq_nonneg ((K:ℝ)-3)]
  have hden2:1≤200*(K:ℝ)^2:=by nlinarith [sq_nonneg ((K:ℝ)-3)]
  have hfrac:θ/(100*(K:ℝ)^2)≤θ:=div_le_self hθ hden
  have hfrac2:θ/(200*(K:ℝ)^2)≤θ:=div_le_self hθ hden2
  have hprod:lam*(θ/(100*(K:ℝ)^2))≤lam*θ:=mul_le_mul_of_nonneg_left hfrac hlam
  have hlam1:lam≤1:=hlamθ.trans hθ1
  have hprod2:lam*θ≤θ:=by nlinarith [mul_nonneg (sub_nonneg.mpr hlam1) hθ]
  have hepsθ:epsOrd≤θ:=by nlinarith only [heps,hprod,hprod2,hθ]
  have ha:alphaOrd≤θ:=(min_le_right _ _).trans hfrac2
  have hg:gammaOrd≤θ:=(min_le_left _ _).trans (by linarith)
  exact ⟨ha,hg,by linarith⟩
end Oberwolfach
