module

public import Oberwolfach.MarkedMatchingCorrectionReserveBudgets

@[expose] public section
/-! Choose correction losses after the level steps and the matching loss cap.
The reserve allowance is kept below both level budgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_matching_correction_late_loss_budget
    (r:ℕ) (gammaStep sigmaStep ζOrd ζRob:ℝ)
    (hγ:0<gammaStep) (hσ:0<sigmaStep) (hOrd:0<ζOrd) (hRob:0<ζRob):
    ∃gammaLoss sigmaLoss extra ζCorr:ℝ,
      0<gammaLoss ∧ 0<sigmaLoss ∧ 0<extra ∧ gammaLoss≤ζOrd/2 ∧
      gammaLoss+extra≤gammaStep ∧ sigmaLoss+extra≤sigmaStep ∧
      0<ζCorr ∧ ζCorr≤ζRob ∧
      (∀ξ:ℝ,16*((((r+4):ℕ):ℝ)+1)*ξ≤ζCorr→∀n:ℕ,
        6*(8*((((r+4):ℕ):ℝ)+1)*ξ*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
      (∀e:ℕ,∃N:ℕ,∀n≥N,(e:ℝ)≤extra*n):=by
  let base:=min gammaStep sigmaStep
  let loss:=min base ζOrd/4
  let extra:=base/2
  have hbase:0<base:=by dsimp [base];positivity
  have hloss:0<loss:=by dsimp [loss];positivity
  have hextra:0<extra:=by dsimp [extra];positivity
  have hbaseγ:base≤gammaStep:=min_le_left _ _
  have hbaseσ:base≤sigmaStep:=min_le_right _ _
  have hlossbase:loss≤base/4:=by
    dsimp [loss];exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hlossOrd:loss≤ζOrd/2:=by
    dsimp [loss];have hh:=min_le_right base ζOrd;linarith
  have hγsum:loss+extra≤gammaStep:=by dsimp [extra];linarith
  have hσsum:loss+extra≤sigmaStep:=by dsimp [extra];linarith
  obtain ⟨ζCorr,hζCorr,hζcap,hinc⟩:=
    marked_correction_robust_budget_choice r ζRob loss loss hRob hloss hloss
  refine ⟨loss,loss,extra,ζCorr,hloss,hloss,hextra,hlossOrd,hγsum,hσsum,hζCorr,hζcap,hinc,?_⟩
  intro e
  obtain ⟨N,hN⟩:=exists_nat_ge ((e:ℝ)/extra)
  refine ⟨N,?_⟩
  intro n hn
  have hnn:(N:ℝ)≤n:=by exact_mod_cast hn
  have heq:(e:ℝ)/extra≤n:=hN.trans hnn
  simpa only [mul_comm] using (div_le_iff₀ hextra).mp heq
end Oberwolfach
