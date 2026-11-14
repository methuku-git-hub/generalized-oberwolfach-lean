module

public import Oberwolfach.LongCorrectionStrictBudgetSpacing
public import Oberwolfach.LongSelectorMatchingRatesBound

@[expose] public section
/-! Select the correction scales with enough room for both the physical rim
changes and the independent retained-spoke changes. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem long_shared_rim_spoke_budget_choice
    (r:ℕ) (ρ₀ cap εInner:ℝ) (hρ₀:0<ρ₀) (hcap:0<cap)
    (hInner:εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    let c:=min cap (1:ℝ);
    ∃ rho eta ζ Δ δLoss δglobal θ t:ℝ,
      0<rho ∧ 0<eta ∧ 0<ζ ∧ 0<Δ ∧ 0<δLoss ∧ 0<δglobal ∧ 0<θ ∧ 0<t ∧
      θ≤t ∧ θ≤Δ ∧ eta≤rho ∧ 5*Real.sqrt δglobal≤δLoss ∧ 10*θ≤δglobal ∧
      θ≤c/1024 ∧ δglobal+Real.sqrt δglobal≤c/1024 ∧
      ∀ (K d:ℕ) (lam epsOrd ζOrd ξClass:ℝ),
        3≤K→0≤lam→lam≤θ→
        3*epsOrd≤lam*(θ/(100*(K:ℝ)^2))→ζOrd≤epsOrd/8→ξClass≤t→
        let alphaOrd:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
        let gammaOrd:=min (epsOrd/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
        ζOrd+δLoss<eta ∧ rho+ζOrd+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
        2*θ+2*max alphaOrd (4*gammaOrd)+2*ξClass+5*Real.sqrt δglobal+2*ζOrd+(1+2/rho)*eta<c/2048 ∧
        ∀ ζret refRate:ℝ,ζret≤c/1024→ refRate≤c/1024→
          2*(ζret+δglobal+Real.sqrt δglobal)+refRate+2*(c/1024)<c/2 ∧
          2*(ζret+10*θ)+refRate≤c/2 :=by
  intro c
  have hc:0<c:=by dsimp [c];exact lt_min hcap (by norm_num)
  have hc1:c≤1:=min_le_right _ _
  obtain ⟨rho,eta,ζ,Δ,δLoss,δglobal,θ,t,hrho,heta,hζ,hΔ,hδLoss,hδglobal,hθ,ht,
    hθt,hθΔ,hΔζ,hηrho,hbudget,hsupply,hsqrt,hspacing,hζcap,hstrict⟩:=
      long_correction_strict_budget_given_inner_with_spacing r ρ₀ (c/2048) εInner hρ₀ (by positivity) hInner
  have hroot:0≤Real.sqrt δglobal:=Real.sqrt_nonneg _
  have hterm:0≤(1+2/rho)*eta:=by positivity
  have hbase:=hstrict 0 0 0 ht.le ht.le ht.le
  norm_num only [mul_zero,max_self,add_zero] at hbase
  have hθsmall:θ≤c/1024:=by nlinarith only [hbase,hθ,hΔ,hroot,hterm]
  have hrootSmall:Real.sqrt δglobal≤c/10240:=by nlinarith only [hbase,hθ,hΔ,hroot,hterm]
  have hroot1:Real.sqrt δglobal≤1:=by nlinarith only [hrootSmall,hc1]
  have hsquare:=Real.sq_sqrt hδglobal.le
  have hδroot:δglobal≤Real.sqrt δglobal:=by nlinarith [mul_nonneg hroot (sub_nonneg.mpr hroot1)]
  have hδsum:δglobal+Real.sqrt δglobal≤c/1024:=by nlinarith only [hδroot,hrootSmall,hc]
  have hθ1:θ≤1:=by nlinarith only [hθsmall,hc1]
  refine ⟨rho,eta,ζ,Δ,δLoss,δglobal,θ,t,hrho,heta,hζ,hΔ,hδLoss,hδglobal,hθ,ht,
    hθt,hθΔ,hηrho,hsqrt,hspacing,hθsmall,hδsum,?_⟩
  intro K d lam epsOrd ζOrd ξClass hK hlam hlamθ heps hζOrd hξClass alphaOrd gammaOrd
  obtain ⟨ha,hg,hζθ⟩:=long_selector_matching_rates_bound K d θ lam epsOrd ζOrd hK hθ.le hθ1 hlam hlamθ heps hζOrd
  have hζΔ:ζOrd≤Δ:=hζθ.trans hθΔ
  have hζζ:ζOrd≤ζ:=hζΔ.trans_eq hΔζ
  have hstrict':=hstrict alphaOrd gammaOrd ξClass (ha.trans hθt) (hg.trans hθt) hξClass
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  intro ζret refRate hret href
  constructor <;> linarith only [hc,hθsmall,hδsum,hret,href]
end Oberwolfach
