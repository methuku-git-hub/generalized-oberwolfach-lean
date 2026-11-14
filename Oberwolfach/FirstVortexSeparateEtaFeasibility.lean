module

public import Mathlib.Tactic

@[expose] public section
/-! The separated global and local matching errors admit the degree-loss
and local transfer margins when the displayed cap is fixed first. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_separate_eta_feasibility
    (c rho:ℝ) (hc:0<c) (hrho:0<rho):
    ∃δsmall ε etaGlobal δLoss:ℝ,
      0<δsmall ∧ 0<ε ∧ ε<δsmall/4 ∧
      0<δLoss ∧ 2*δsmall<δLoss ∧ δLoss<etaGlobal ∧ etaGlobal≤c*rho/4 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→∀κ:ℝ,0≤κ→κ≤δsmall/4→
        2*(δsmall*n+(κ*n+1))≤δLoss*n :=by
  let δsmall:ℝ:=min (c*rho/100) 1
  let ε:ℝ:=δsmall/8
  let δLoss:ℝ:=3*δsmall
  let etaGlobal:ℝ:=c*rho/8
  have hδ:0<δsmall:=by dsimp [δsmall];positivity
  have hδcap:δsmall≤c*rho/100:=min_le_left _ _
  have he:0<ε:=by dsimp [ε];positivity
  have hegap:ε<δsmall/4:=by dsimp [ε];linarith
  have hLoss:0<δLoss:=by dsimp [δLoss];positivity
  have hLossLo:2*δsmall<δLoss:=by dsimp [δLoss];linarith
  have hLossHi:δLoss<etaGlobal:=by dsimp [δLoss,etaGlobal];have hp:0<c*rho:=mul_pos hc hrho;linarith
  have hEta:etaGlobal≤c*rho/4:=by dsimp [etaGlobal];have hp:0<c*rho:=mul_pos hc hrho;linarith
  obtain ⟨N,hN⟩:=exists_nat_gt (4/δsmall)
  refine ⟨δsmall,ε,etaGlobal,δLoss,hδ,he,hegap,hLoss,hLossLo,hLossHi,hEta,N,?_⟩
  intro n hn κ hκ hκcap
  have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
  have hNn:4/δsmall<(n:ℝ):=lt_of_lt_of_le hN hnR
  have hscale:4<δsmall*n:=by have hh:=(div_lt_iff₀ hδ).mp hNn;nlinarith
  have hκn:=mul_le_mul_of_nonneg_right hκcap (show (0:ℝ)≤n by positivity)
  dsimp [δLoss]
  nlinarith
end Oberwolfach
