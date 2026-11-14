module

public import Oberwolfach.FirstVortexSharedRobustDualBudgetChoice
public import Oberwolfach.FirstVortexAmbientLossBudget

@[expose] public section
/-! The ambient loss is fixed before the local balance scale.  Shrinking the
inner-size rate makes the protected-degree and deletion budgets compatible
with the same earlier choice. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_ambient_global_hierarchy
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hcap:0<cap) (hβ:0<βfinal):
    let c:=min cap (1:ℝ);
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ,
      0<rho ∧ 0<eta ∧ 0<ζmax ∧ 0<Δmax ∧ 0<δLoss ∧ 0<εInner ∧
      0<δglobal ∧ 0<θmax ∧ 0<t ∧ eta≤rho ∧ εInner≤δglobal/8 ∧
      5*Real.sqrt δglobal≤δLoss ∧ δglobal≤(βfinal/100)^2 ∧
      10*θmax≤δglobal ∧ θmax≤c/1024 ∧ δglobal+Real.sqrt δglobal≤c/1024 ∧ ζmax≤cap ∧
      (∀ζ:ℝ,0≤ζ→ζ≤ζmax→ζ+δLoss<eta ∧
        rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))) ∧
      (∀θ Δ a γ ξClass:ℝ,θ≤θmax→Δ≤Δmax→a≤t→γ≤t→ξClass≤t→
        2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<c/2048) ∧
      (∀θ ζret refRate:ℝ,θ≤θmax→ζret≤c/1024→ refRate≤c/1024→
        2*(ζret+δglobal+Real.sqrt δglobal)+refRate+2*(c/1024)<c/2 ∧
        2*(ζret+10*θ)+refRate≤c/2) ∧
      ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→∀κ:ℝ,0≤κ→κ≤Real.sqrt δglobal/4→
        δglobal+κ≤Real.sqrt δglobal ∧
        2*(δglobal*(n:ℝ)+(κ*(n:ℝ)+1))≤δLoss*(n:ℝ) ∧
        εInner*(n:ℝ)+((6*d+2:ℕ):ℝ)≤δglobal*(n:ℝ)/4 :=by
  intro c
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εOld,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθ,ht,hetaR,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,hBudget,hChange,hRows⟩:=
    first_vortex_shared_robust_dual_budget_choice r ρ₀ cap βfinal hρ₀ hcap hβ
  let εInner:=min εOld (δglobal/8)
  have hInner':0<εInner:=by dsimp [εInner];positivity
  have hInnerOld:εInner≤εOld:=min_le_left _ _
  have hInnerδ:εInner≤δglobal/8:=min_le_right _ _
  have hc1:c≤1:=min_le_right _ _
  have hsqrt:0≤Real.sqrt δglobal:=Real.sqrt_nonneg _
  have hδsmall:δglobal≤1/4:=by linarith
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner',hglobal,hθ,ht,hetaR,hInnerδ,hLossScale,hδbound,hθglobal,hθsmall,hδsum,hζcap,?_,hChange,hRows,?_⟩
  · intro ζ hζ0 hζmax
    obtain ⟨hfirst,hsecond⟩:=hBudget ζ hζ0 hζmax
    exact ⟨hfirst,by linarith⟩
  · intro d
    obtain ⟨N,hN⟩:=first_vortex_ambient_loss_budget δglobal δLoss d hglobal hδsmall hLossScale
    exact ⟨N,fun n hn κ hκ hκcap=>hN n hn κ εInner hκ hκcap hInner'.le hInnerδ⟩
end Oberwolfach
