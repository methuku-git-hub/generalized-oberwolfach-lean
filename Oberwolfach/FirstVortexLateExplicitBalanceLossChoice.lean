module

public import Oberwolfach.MarkedExplicitJointBalanceBoundaryBudget
public import Oberwolfach.FirstVortexSeparateLossMarginChoice

@[expose] public section
/-! If the global load scale may be selected after the balance windows,
all separated-loss margins can be chosen simultaneously. This lemma does
not assert that the surrounding construction permits that order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_late_explicit_balance_loss_choice
    (m h:ℕ) (etaBal x rho globalCap δCap:ℝ)
    (hη:0<etaBal) (hx:0<x) (hrho:0<rho) (hGlobal:0<globalCap) (hδCap:0<δCap):
    ∃δsmall:ℝ,0<δsmall ∧ δsmall≤δCap ∧
      ∃etaGlobal δLoss:ℝ,0<etaGlobal ∧ etaGlobal≤rho ∧
        etaGlobal≤markedExplicitJointLocalCap m h etaBal x*rho/4 ∧
        2*(1+2/rho)*etaGlobal≤globalCap/2 ∧
        0<δLoss ∧ 2*δsmall<δLoss ∧
        (∀Δ:ℝ,Δ≤δsmall/4→Δ+δLoss<etaGlobal) ∧
        ∃N:ℕ,∀n:ℕ,N≤n→∀κ:ℝ,κ≤δsmall/4→
          2*(δsmall*n+(κ*n+1))≤δLoss*n :=by
  have hc:0<markedExplicitJointLocalCap m h etaBal x:=
    (marked_explicit_joint_balance_boundary_budget m h etaBal x hη hx).1
  have hfactor:0<20*(1+2/rho):=by positivity
  let δsmall:=min (δCap/2) (min (markedExplicitJointLocalCap m h etaBal x*rho/80)
    (min (rho/20) (globalCap/(4*(20*(1+2/rho))))))
  have hδ:0<δsmall:=by dsimp [δsmall];positivity
  have hδCap:δsmall≤δCap:=by
    have h:=min_le_left (δCap/2) (min (markedExplicitJointLocalCap m h etaBal x*rho/80)
      (min (rho/20) (globalCap/(4*(20*(1+2/rho))))))
    dsimp [δsmall];linarith
  have hδLocal:40*δsmall≤markedExplicitJointLocalCap m h etaBal x*rho:=by
    have h:= (min_le_right (δCap/2) (min (markedExplicitJointLocalCap m h etaBal x*rho/80)
      (min (rho/20) (globalCap/(4*(20*(1+2/rho))))))).trans (min_le_left _ _)
    dsimp [δsmall];linarith
  have hδRho:10*δsmall≤rho:=by
    have h:= (min_le_right (δCap/2) (min (markedExplicitJointLocalCap m h etaBal x*rho/80)
      (min (rho/20) (globalCap/(4*(20*(1+2/rho))))))).trans ((min_le_right _ _).trans (min_le_left _ _))
    dsimp [δsmall];linarith
  have hδGlobal:20*(1+2/rho)*δsmall≤globalCap/2:=by
    have h:= (min_le_right (δCap/2) (min (markedExplicitJointLocalCap m h etaBal x*rho/80)
      (min (rho/20) (globalCap/(4*(20*(1+2/rho))))))).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hm:=mul_le_mul_of_nonneg_left h hfactor.le
    have heq:20*(1+2/rho)*(globalCap/(4*(20*(1+2/rho))))=globalCap/4:=by field_simp
    rw [heq] at hm
    dsimp [δsmall];linarith
  exact ⟨δsmall,hδ,hδCap,first_vortex_separate_loss_margin_choice δsmall _ rho globalCap hδ hrho hδLocal hδRho hδGlobal⟩
end Oberwolfach
