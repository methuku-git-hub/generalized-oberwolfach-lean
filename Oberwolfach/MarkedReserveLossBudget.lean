module

public import Mathlib.Tactic

@[expose] public section
/-! After the first loss is fixed with slack and the second loss cap is
known, choose a reserve allowance before its size and the host order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_reserve_loss_budget_choice
    (gammaLoss gammaMax sigmaMax:ℝ)
    (hγ:0<gammaLoss) (hγgap:gammaLoss<gammaMax) (hσ:0<sigmaMax):
    ∃ sigmaLoss extra:ℝ,0<sigmaLoss ∧ 0<extra ∧
      gammaLoss+extra≤gammaMax ∧ sigmaLoss+extra≤sigmaMax ∧
      ∀ e:ℕ,∃ N:ℕ,∀ n≥N,(e:ℝ)≤extra*n:=by
  let sigmaLoss:=sigmaMax/2
  let extra:=min (gammaMax-gammaLoss) (sigmaMax/2)/2
  have hgap:0<gammaMax-gammaLoss:=sub_pos.mpr hγgap
  have he:0<extra:=by dsimp [extra];positivity
  have hs:0<sigmaLoss:=by dsimp [sigmaLoss];positivity
  have heγ:extra≤(gammaMax-gammaLoss)/2:=by dsimp [extra];exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have heσ:extra≤(sigmaMax/2)/2:=by dsimp [extra];exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  refine ⟨sigmaLoss,extra,hs,he,by linarith,by dsimp [sigmaLoss];linarith,?_⟩
  intro e
  obtain ⟨N,hN⟩:=exists_nat_ge ((e:ℝ)/extra)
  refine ⟨N,?_⟩
  intro n hn
  have hnn:(N:ℝ)≤n:=by exact_mod_cast hn
  have heq:(e:ℝ)/extra≤n:=hN.trans hnn
  simpa only [mul_comm] using (div_le_iff₀ he).mp heq
end Oberwolfach
