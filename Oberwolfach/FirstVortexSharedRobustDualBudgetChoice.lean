module

public import Oberwolfach.FirstVortexRobustDualBudgetChoice

@[expose] public section
/-! The correction parameters also leave the stronger row and column slack
needed to transfer the global robust event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_shared_robust_dual_budget_choice
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hcap:0<cap) (hβ:0<βfinal):
    let c:=min cap (1:ℝ);
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ,
      0<rho ∧ 0<eta ∧ 0<ζmax ∧ 0<Δmax ∧ 0<δLoss ∧ 0<εInner ∧
      0<δglobal ∧ 0<θmax ∧ 0<t ∧ eta≤rho ∧
      5*Real.sqrt δglobal≤δLoss ∧ δglobal≤(βfinal/100)^2 ∧
      10*θmax≤δglobal ∧ θmax≤c/1024 ∧ δglobal+Real.sqrt δglobal≤c/1024 ∧ ζmax≤cap ∧
      (∀ζ:ℝ,0≤ζ→ζ≤ζmax→ζ+δLoss<eta ∧
        rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))) ∧
      (∀θ Δ a γ ξClass:ℝ,θ≤θmax→Δ≤Δmax→a≤t→γ≤t→ξClass≤t→
        2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<c/2048) ∧
      ∀θ ζret refRate:ℝ,θ≤θmax→ζret≤c/1024→ refRate≤c/1024→
        2*(ζret+δglobal+Real.sqrt δglobal)+refRate+2*(c/1024)<c/2 ∧
        2*(ζret+10*θ)+refRate≤c/2 :=by
  intro c
  have hc:0<c:=by dsimp [c];positivity
  have hc1:c≤1:=min_le_right _ _
  have hccap:c≤cap:=min_le_left _ _
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθ,ht,hetaR,hLossScale,hδbound,hθglobal,hζcap,hBudget,hChange⟩:=
    first_vortex_robust_dual_budget_choice r ρ₀ (c/2048) βfinal hρ₀ (by positivity) hβ
  have hbase:=hChange θmax Δmax 0 0 0 (le_refl _) (le_refl _) ht.le ht.le ht.le
  norm_num only [mul_zero,max_self,add_zero] at hbase
  have hroot:0≤Real.sqrt δglobal:=Real.sqrt_nonneg _
  have hterm:0≤(1+2/rho)*eta:=by positivity
  have hθsmall:θmax≤c/1024:=by nlinarith only [hbase,hθ,hΔ,hroot,hterm]
  have hrootSmall:Real.sqrt δglobal≤c/10240:=by nlinarith only [hbase,hθ,hΔ,hroot,hterm]
  have hroot1:Real.sqrt δglobal≤1:=by nlinarith only [hrootSmall,hc1]
  have hsquare:=Real.sq_sqrt hglobal.le
  have hδroot:δglobal≤Real.sqrt δglobal:=by nlinarith [mul_nonneg hroot (sub_nonneg.mpr hroot1)]
  have hδsum:δglobal+Real.sqrt δglobal≤c/1024:=by nlinarith only [hδroot,hrootSmall,hc]
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθ,ht,hetaR,hLossScale,hδbound,hθglobal,hθsmall,hδsum,?_,hBudget,hChange,?_⟩
  · have hh:c/2048≤cap:=by linarith
    exact hζcap.trans hh
  · intro θ ζret refRate hθle hret href
    constructor <;> linarith only [hc,hθsmall,hθle,hδsum,hret,href]
end Oberwolfach
