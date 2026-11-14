module

public import Oberwolfach.LongCorrectionStrictBudgetSpacing
public import Oberwolfach.LongSelectorMatchingRatesBound

@[expose] public section
/-! Choose the correction budget before spacing, then use the actual rates
returned by the matching selector without identifying its loss with an
independently chosen upper bound. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem long_correction_budget_for_selector_rates
    (r:ℕ) (ρ₀ cap εInner:ℝ) (hρ₀:0<ρ₀) (hcap:0<cap)
    (hInner:εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    ∃ rho eta ζ Δ δLoss δglobal θ t:ℝ,
      0<rho ∧ 0<eta ∧ 0<ζ ∧ 0<Δ ∧ 0<δLoss ∧ 0<δglobal ∧ 0<θ ∧ 0<t ∧
      θ≤t ∧ θ≤Δ ∧ eta≤rho ∧ 5*Real.sqrt δglobal≤δLoss ∧ 10*θ≤δglobal ∧ ζ≤cap ∧
      ∀ (K d:ℕ) (lam epsOrd ζOrd ξClass:ℝ),
        3≤K→θ≤1→0≤lam→lam≤θ→
        3*epsOrd≤lam*(θ/(100*(K:ℝ)^2))→ζOrd≤epsOrd/8→ξClass≤t→
        let alphaOrd:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
        let gammaOrd:=min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
        ζOrd+δLoss<eta ∧ rho+ζOrd+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
        2*θ+2*max alphaOrd (4*gammaOrd)+2*ξClass+5*Real.sqrt δglobal+2*ζOrd+(1+2/rho)*eta<cap :=by
  obtain ⟨rho,eta,ζ,Δ,δLoss,δglobal,θ,t,hrho,heta,hζ,hΔ,hδLoss,hδglobal,hθ,ht,
    hθt,hθΔ,hΔζ,hηrho,hbudget,hsupply,hsqrt,hspacing,hζcap,hstrict⟩:=
      long_correction_strict_budget_given_inner_with_spacing r ρ₀ cap εInner hρ₀ hcap hInner
  refine ⟨rho,eta,ζ,Δ,δLoss,δglobal,θ,t,hrho,heta,hζ,hΔ,hδLoss,hδglobal,hθ,ht,
    hθt,hθΔ,hηrho,hsqrt,hspacing,hζcap,?_⟩
  intro K d lam epsOrd ζOrd ξClass hK hθ1 hlam hlamθ heps hζOrd hξClass alphaOrd gammaOrd
  obtain ⟨ha,hg,hζθ⟩:=long_selector_matching_rates_bound K d θ lam epsOrd ζOrd hK hθ.le hθ1 hlam hlamθ heps hζOrd
  have hζΔ:ζOrd≤Δ:=hζθ.trans hθΔ
  have hζζ:ζOrd≤ζ:=hζΔ.trans_eq hΔζ
  have hh:=hstrict alphaOrd gammaOrd ξClass (ha.trans hθt) (hg.trans hθt) hξClass
  exact ⟨by linarith,by linarith,by linarith⟩
end Oberwolfach
