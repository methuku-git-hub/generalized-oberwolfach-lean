module

public import Oberwolfach.FirstVortexLateExplicitBalanceLossChoice
public import Oberwolfach.FirstVortexLateSpacingStrictChoice

@[expose] public section
/-! Late selection of the load and matching spacing after the two balance
windows. Applying this requires the surrounding parameters to be independent
of the subsequently selected matching spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_late_balance_loss_spacing_choice
    (r:ℕ) (etaBal x rho globalCap δCap θCap ε active cBoundary:ℝ)
    (hη:0<etaBal) (hx:0<x) (hrho:0<rho) (hGlobal:0<globalCap)
    (hδCap:0<δCap) (hθCap:0<θCap) (hε:0<ε) (hactive:0<active) (hboundary:0<cBoundary):
    ∃δsmall etaGlobal δLoss θ:ℝ,0<δsmall ∧ δsmall≤δCap ∧
      0<etaGlobal ∧ etaGlobal≤rho ∧
      etaGlobal≤markedExplicitJointLocalCap (r+4) (r+12) etaBal x*rho/4 ∧
      2*(1+2/rho)*etaGlobal≤globalCap/2 ∧
      0<δLoss ∧ 2*δsmall<δLoss ∧
      (∀Δ:ℝ,Δ≤δsmall/4→Δ+δLoss<etaGlobal) ∧
      (∃N:ℕ,∀n:ℕ,N≤n→∀κ:ℝ,κ≤δsmall/4→
        2*(δsmall*n+(κ*n+1))≤δLoss*n) ∧
      0<θ ∧ θ≤θCap ∧ 10*θ≤δsmall ∧
      ∃dMin:ℕ,∀d:ℕ,dMin≤d→3≤d ∧ (r+4)+2≤d ∧
        1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
        4/(d:ℝ)<cBoundary ∧ (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
        ∃KMin:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
          5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 :=by
  obtain ⟨δsmall,hδ,hδcap,etaGlobal,δLoss,he,her,hel,heg,hl,hlo,hΔ,N,hN⟩:=
    first_vortex_late_explicit_balance_loss_choice (r+4) (r+12) etaBal x rho globalCap δCap hη hx hrho hGlobal hδCap
  let θ:=min (θCap/2) (δsmall/20)
  have hθ:0<θ:=by dsimp [θ];positivity
  have hθCap':θ≤θCap:=by dsimp [θ];have hh:=min_le_left (θCap/2) (δsmall/20);linarith
  have hθδ:10*θ≤δsmall:=by dsimp [θ];have hh:=min_le_right (θCap/2) (δsmall/20);linarith
  obtain ⟨dMin,hd⟩:=first_vortex_late_spacing_and_class_strict_choice r θ ε active cBoundary hθ hε hactive hboundary
  exact ⟨δsmall,etaGlobal,δLoss,θ,hδ,hδcap,he,her,hel,heg,hl,hlo,hΔ,⟨N,hN⟩,hθ,hθCap',hθδ,dMin,hd⟩
end Oberwolfach
