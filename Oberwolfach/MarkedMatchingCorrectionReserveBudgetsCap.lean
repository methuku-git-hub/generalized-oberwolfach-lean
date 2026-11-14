module

public import Oberwolfach.MarkedMatchingCorrectionReserveBudgets

@[expose] public section

/-! The first cover-down loss can be chosen below an arbitrary positive
matching allowance fixed earlier, without changing the later reserve choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_matching_correction_reserve_budget_choice_capped
    (r:ℕ) (gammaMax gammaCap ζRob:ℝ) (hγ:0<gammaMax) (hcap:0<gammaCap) (hζ:0<ζRob):
    ∃ gammaStep:ℝ,0<gammaStep ∧ gammaStep≤gammaMax ∧ gammaStep≤gammaCap ∧
    ∀ sigmaMax:ℝ,0<sigmaMax→
    ∃ sigmaStep gammaLoss sigmaLoss extra ζCorr:ℝ,
      0<sigmaStep ∧ sigmaStep≤sigmaMax ∧ 0<gammaLoss ∧ 0<sigmaLoss ∧ 0<extra ∧
      gammaLoss+extra=gammaStep ∧ sigmaLoss+extra=sigmaStep ∧ 0<ζCorr ∧ ζCorr≤ζRob ∧
      (∀ ξ:ℝ,16*((((r+4):ℕ):ℝ)+1)*ξ≤ζCorr→∀n:ℕ,
        6*(8*((((r+4):ℕ):ℝ)+1)*ξ*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
      (∀e:ℕ,∃N:ℕ,∀n≥N,(e:ℝ)≤extra*n) := by
  obtain ⟨gammaStep,hpos,hbound,hrest⟩:=marked_matching_correction_reserve_budget_choice r (min gammaMax gammaCap) ζRob (lt_min hγ hcap) hζ
  exact ⟨gammaStep,hpos,hbound.trans (min_le_left _ _),hbound.trans (min_le_right _ _),hrest⟩
end Oberwolfach
