module

public import Oberwolfach.LongCorrectionStrictChangeBudgetChoice

@[expose] public section
/-! One ordered choice supplies the dual correction, the square-root loss,
the terminal-list scale and the global robustness change cap. Later matching
and spacing tolerances may be chosen smaller. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_robust_dual_budget_choice
    (r:ℕ) (ρ₀ cap βfinal:ℝ) (hρ₀:0<ρ₀) (hcap:0<cap) (hβ:0<βfinal):
    ∃rho eta ζmax Δmax δLoss εInner δglobal θmax t:ℝ,
      0<rho ∧ 0<eta ∧ 0<ζmax ∧ 0<Δmax ∧ 0<δLoss ∧ 0<εInner ∧
      0<δglobal ∧ 0<θmax ∧ 0<t ∧ eta≤rho ∧
      5*Real.sqrt δglobal≤δLoss ∧ δglobal≤(βfinal/100)^2 ∧
      10*θmax≤δglobal ∧ ζmax≤cap ∧
      (∀ζ:ℝ,0≤ζ→ζ≤ζmax→ζ+δLoss<eta ∧
        rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))) ∧
      ∀θ Δ a γ ξClass:ℝ, θ≤θmax→Δ≤Δmax→a≤t→γ≤t→ξClass≤t→
        2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<cap :=by
  let c:=min cap (βfinal/100)
  have hc:0<c:=by dsimp [c];positivity
  have hccap:c≤cap:=min_le_left _ _
  have hcβ:c≤βfinal/100:=min_le_right _ _
  obtain ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθ,ht,hetaR,hbudget,hsupply,hLossScale,hθglobal,hζcap,hChange⟩:=
    long_correction_strict_change_budget_choice r ρ₀ c hρ₀ hc
  have hgap0:=hChange 0 0 0 (by linarith) (by linarith) (by linarith)
  have hlast:0≤(1+2/rho)*eta:=by positivity
  have hsqrt:Real.sqrt δglobal≤βfinal/100:=by
    simp only [mul_zero,max_self,add_zero] at hgap0
    nlinarith only [hgap0,hθ,hΔ,hlast,hcβ,Real.sqrt_nonneg δglobal]
  have hδbound:δglobal≤(βfinal/100)^2:=
    (Real.sqrt_le_iff.mp hsqrt).2
  refine ⟨rho,eta,ζmax,Δmax,δLoss,εInner,δglobal,θmax,t,
    hrho,heta,hζ,hΔ,hLoss,hInner,hglobal,hθ,ht,hetaR,hLossScale,hδbound,hθglobal,hζcap.trans hccap,?_,?_⟩
  · intro ζ hζ0 hζmax
    exact ⟨by linarith,by linarith⟩
  · intro θ Δ a γ ξ hθle hΔle ha hγ hξ
    have hh:=hChange a γ ξ ha hγ hξ
    linarith only [hh,hθle,hΔle,hccap]
end Oberwolfach
