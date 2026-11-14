module

public import Oberwolfach.MarkedCommonCorrectionBudgetChoices

@[expose] public section
/-! Fix the first iteration loss before its second cap is known; then split
both fixed iteration losses into a correction allowance and one reserve. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_matching_correction_reserve_budget_choice
    (r:ℕ) (gammaMax ζRob:ℝ) (hγ:0<gammaMax) (hζ:0<ζRob):
    ∃ gammaStep:ℝ,0<gammaStep ∧ gammaStep≤gammaMax ∧
    ∀ sigmaMax:ℝ,0<sigmaMax→
    ∃ sigmaStep gammaLoss sigmaLoss extra ζCorr:ℝ,
      0<sigmaStep ∧ sigmaStep≤sigmaMax ∧ 0<gammaLoss ∧ 0<sigmaLoss ∧ 0<extra ∧
      gammaLoss+extra=gammaStep ∧ sigmaLoss+extra=sigmaStep ∧ 0<ζCorr ∧ ζCorr≤ζRob ∧
      (∀ ξ:ℝ,16*((((r+4):ℕ):ℝ)+1)*ξ≤ζCorr→∀n:ℕ,
        6*(8*((((r+4):ℕ):ℝ)+1)*ξ*n)≤min (gammaLoss*n) (sigmaLoss*n)) ∧
      (∀e:ℕ,∃N:ℕ,∀n≥N,(e:ℝ)≤extra*n) := by
  let gammaStep:=gammaMax/2
  have hγstep:0<gammaStep:=by dsimp [gammaStep];positivity
  have hγcap:gammaStep≤gammaMax:=by dsimp [gammaStep];linarith
  refine ⟨gammaStep,hγstep,hγcap,?_⟩
  intro sigmaMax hσ
  let sigmaStep:=sigmaMax/2
  let extra:=min gammaStep sigmaStep/2
  let gammaLoss:=gammaStep-extra
  let sigmaLoss:=sigmaStep-extra
  have hσstep:0<sigmaStep:=by dsimp [sigmaStep];positivity
  have hσcap:sigmaStep≤sigmaMax:=by dsimp [sigmaStep];linarith
  have hextra:0<extra:=by dsimp [extra];positivity
  have heγ:extra≤gammaStep/2:=by
    dsimp [extra]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have heσ:extra≤sigmaStep/2:=by
    dsimp [extra]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hγloss:0<gammaLoss:=by dsimp [gammaLoss];linarith
  have hσloss:0<sigmaLoss:=by dsimp [sigmaLoss];linarith
  obtain ⟨ζCorr,hζCorr,hζcap,hinc⟩:=
    marked_correction_robust_budget_choice r ζRob gammaLoss sigmaLoss hζ hγloss hσloss
  refine ⟨sigmaStep,gammaLoss,sigmaLoss,extra,ζCorr,hσstep,hσcap,hγloss,hσloss,hextra,
    by dsimp [gammaLoss];ring,by dsimp [sigmaLoss];ring,hζCorr,hζcap,hinc,?_⟩
  intro e
  obtain ⟨N,hN⟩:=exists_nat_ge ((e:ℝ)/extra)
  refine ⟨N,?_⟩
  intro n hn
  have hnn:(N:ℝ)≤n:=by exact_mod_cast hn
  have heq:(e:ℝ)/extra≤n:=hN.trans hnn
  simpa only [mul_comm] using (div_le_iff₀ hextra).mp heq
end Oberwolfach
