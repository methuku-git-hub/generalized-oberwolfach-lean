module

public import Oberwolfach.FirstVortexActualSelectorBudgetBundle

@[expose] public section
/-! A bound established at a smaller local tolerance supplies the caller's
larger prescribed tolerance without changing the chosen loss witnesses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_summed_loss_mono
    (n d:ℕ) (I c₁ c₂ rho eta θ a γ ξPart κ Δ ζret ηBalance boundary:ℝ)
    (hI:0≤I) (hc:c₁≤c₂)
    (h:FirstVortexSummedLossWitness n d I c₁ rho eta θ a γ ξPart κ Δ ζret ηBalance boundary):
    FirstVortexSummedLossWitness n d I c₂ rho eta θ a γ ξPart κ Δ ζret ηBalance boundary :=by
  obtain ⟨lossInside,inside,loc,hLoss,hInside,hLoc,hLocBound,hInsideBound,hNonneg,hSum,hInsideBudget,hLocalBudget,hLocal,hSpoke⟩:=h
  refine ⟨lossInside,inside,loc,hLoss,hInside,hLoc,hLocBound,hInsideBound,hNonneg,hSum,hInsideBudget,hLocalBudget,?_,?_⟩
  · exact hLocal.trans (mul_le_mul_of_nonneg_right hc hI)
  · exact hSpoke.trans (mul_le_mul_of_nonneg_right hc hI)

theorem first_vortex_joint_local_transfer_caps (localCap transferCap globalCap:ℝ)
    (hlocal:0<localCap) (htransfer:0<transferCap) (hglobal:0<globalCap):
    let chosenLocal:=min localCap (4*transferCap)
    let c:=min chosenLocal globalCap
    let active:=c/4;
    0<chosenLocal ∧ chosenLocal≤localCap ∧ 0<c ∧ 0<active ∧
      active≤localCap ∧ active≤transferCap ∧ active≤globalCap/2 :=by
  intro chosenLocal c active
  have hl:0<chosenLocal:=by dsimp [chosenLocal]; positivity
  have hl0:chosenLocal≤localCap:=min_le_left _ _
  have hlt:chosenLocal≤4*transferCap:=min_le_right _ _
  have hc:0<c:=by dsimp [c]; positivity
  have hcl:c≤chosenLocal:=min_le_left _ _
  have hcg:c≤globalCap:=min_le_right _ _
  refine ⟨hl,hl0,hc,by dsimp [active]; positivity,?_,?_,?_⟩ <;> dsimp [active] <;> linarith
end Oberwolfach
