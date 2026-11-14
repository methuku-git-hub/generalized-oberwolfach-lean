module

public import Mathlib.Tactic

@[expose] public section
/-! A robustness-scale correction fits the two first-level incidence budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_correction_incidence_budget
    (r n:ℕ) (ξ ζ gammaLoss sigmaLoss:ℝ)
    (hscale:16*((((r+4):ℕ):ℝ)+1)*ξ≤ζ)
    (hgap:3*ζ≤min gammaLoss sigmaLoss):
    6*(8*((((r+4):ℕ):ℝ)+1)*ξ*n)≤min (gammaLoss*n) (sigmaLoss*n) := by
  have hn:0≤(n:ℝ):=by positivity
  have hs:=mul_le_mul_of_nonneg_right hscale hn
  have hg:=mul_le_mul_of_nonneg_right (hgap.trans (min_le_left _ _)) hn
  have hσ:=mul_le_mul_of_nonneg_right (hgap.trans (min_le_right _ _)) hn
  apply le_min <;> nlinarith only [hs,hg,hσ]
end Oberwolfach
