module

public import Mathlib.Tactic

@[expose] public section
/-! The separated loss rates satisfy the caller's degree-loss hypotheses
once the earlier global load scale fits the later local balance cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_separate_loss_margin_choice
    (δsmall cLocal rho globalCap:ℝ) (hδ:0<δsmall) (hrho:0<rho)
    (hcapLocal:40*δsmall≤cLocal*rho) (hcapRho:10*δsmall≤rho)
    (hcapGlobal:20*(1+2/rho)*δsmall≤globalCap/2):
    ∃etaGlobal δLoss:ℝ,0<etaGlobal ∧ etaGlobal≤rho ∧ etaGlobal≤cLocal*rho/4 ∧
      2*(1+2/rho)*etaGlobal≤globalCap/2 ∧
      0<δLoss ∧ 2*δsmall<δLoss ∧
      (∀Δ:ℝ,Δ≤δsmall/4→Δ+δLoss<etaGlobal) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→∀κ:ℝ,κ≤δsmall/4→
        2*(δsmall*n+(κ*n+1))≤δLoss*n :=by
  let etaGlobal:=10*δsmall
  let δLoss:=4*δsmall
  have heta:0<etaGlobal:=by dsimp [etaGlobal];positivity
  have hetaR:etaGlobal≤rho:=by simpa [etaGlobal] using hcapRho
  have hetaLocal:etaGlobal≤cLocal*rho/4:=by dsimp [etaGlobal];linarith
  have hetaGlobal:2*(1+2/rho)*etaGlobal≤globalCap/2:=by dsimp [etaGlobal];nlinarith [hcapGlobal]
  have hLoss:0<δLoss:=by dsimp [δLoss];positivity
  have hLossLo:2*δsmall<δLoss:=by dsimp [δLoss];linarith
  obtain ⟨N,hN⟩:=exists_nat_gt (4/δsmall)
  refine ⟨etaGlobal,δLoss,heta,hetaR,hetaLocal,hetaGlobal,hLoss,hLossLo,?_,N,?_⟩
  · intro Δ hΔ
    dsimp [etaGlobal,δLoss];linarith
  · intro n hn κ hκ
    have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
    have hNn:4/δsmall<(n:ℝ):=lt_of_lt_of_le hN hnR
    have hscale:4<δsmall*n:=by have hh:=(div_lt_iff₀ hδ).mp hNn;nlinarith
    have hκn:=mul_le_mul_of_nonneg_right hκ (show (0:ℝ)≤n by positivity)
    dsimp [δLoss]
    nlinarith
end Oberwolfach
