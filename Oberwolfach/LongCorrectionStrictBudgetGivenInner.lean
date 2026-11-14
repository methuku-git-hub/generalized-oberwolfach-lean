module

public import Oberwolfach.LongMatchingCorrectionSharedChangeCap

@[expose] public section
/-! A positive hierarchy of correction parameters gives strict slack for
both the dual correction and the shared rim/spoke change cap. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem long_correction_strict_budget_given_inner
    (r:ℕ) (ρ₀ cap εInner:ℝ) (hρ₀:0<ρ₀) (hcap:0<cap)
    (hInner:εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    ∃ rho eta ζ Δ δLoss δglobal θ t:ℝ,
      0<rho ∧ 0<eta ∧ 0<ζ ∧ 0<Δ ∧ 0<δLoss ∧ 0<δglobal ∧ 0<θ ∧ 0<t ∧
      eta≤rho ∧ ζ+δLoss<eta ∧ rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ)) ∧
      5*Real.sqrt δglobal≤δLoss ∧ 10*θ≤δglobal ∧ ζ≤cap ∧
      ∀a γ ξClass:ℝ,a≤t→γ≤t→ξClass≤t→
        2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<cap :=by
  let c:=min (1:ℝ) (min cap (ρ₀/(400*((r+4:ℕ):ℝ))-εInner))
  let rho:=c/16
  let eta:=c^2/4096
  let ζ:=eta/8
  let Δ:=eta/8
  let δLoss:=eta/8
  let δglobal:=(δLoss/10)^2
  let θ:=δglobal/20
  let t:=eta/1000
  have hc:0<c:=by dsimp [c];exact lt_min (by norm_num) (lt_min hcap (sub_pos.mpr hInner))
  have hc1:c≤1:=min_le_left _ _
  have hccap:c≤cap:=(min_le_right _ _).trans (min_le_left _ _)
  have hcsupply:c≤ρ₀/(400*((r+4:ℕ):ℝ))-εInner:=(min_le_right _ _).trans (min_le_right _ _)
  have hc2:c^2≤c:=by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hc1)]
  have hrho:0<rho:=by dsimp [rho];positivity
  have heta:0<eta:=by dsimp [eta];positivity
  have hηc:eta≤c/4096:=by dsimp [eta];nlinarith only [hc2]
  have hη1:eta≤1:=by dsimp [eta];nlinarith only [hc2,hc1]
  have hηrho:eta≤rho:=by dsimp [eta,rho];nlinarith only [hc2]
  have hz:0<ζ:=by dsimp [ζ];positivity
  have hΔ:0<Δ:=by dsimp [Δ];positivity
  have hδ:0<δLoss:=by dsimp [δLoss];positivity
  have hδglobal:0<δglobal:=by dsimp [δglobal];positivity
  have hθ:0<θ:=by dsimp [θ];positivity
  have ht:0<t:=by dsimp [t];positivity
  have hsqrt:Real.sqrt δglobal=δLoss/10:=by
    dsimp [δglobal]
    rw [Real.sqrt_sq_eq_abs,abs_of_pos (by positivity : 0<δLoss/10)]
  have hθsmall:θ≤eta/1000:=by
    dsimp [θ,δglobal,δLoss]
    nlinarith [mul_nonneg heta.le (sub_nonneg.mpr hη1)]
  have hterm:(1+2/rho)*eta=c^2/4096+c/128:=by
    dsimp [rho,eta]
    field_simp
    <;> ring
  refine ⟨rho,eta,ζ,Δ,δLoss,δglobal,θ,t,hrho,heta,hz,hΔ,hδ,hδglobal,hθ,ht,hηrho,?_,?_,?_,?_,?_,?_⟩
  · dsimp [ζ,δLoss];linarith
  · dsimp [rho,ζ,δLoss,eta]
    nlinarith only [hc,hc2,hcsupply]
  · rw [hsqrt];linarith
  · dsimp [θ];linarith
  · dsimp [ζ,eta]
    nlinarith only [hc,hc2,hccap]
  · intro a γ ξ ha hγ hξ
    have hm:max a (4*γ)≤4*t:=max_le (by linarith [ht]) (by linarith)
    rw [hsqrt,hterm]
    dsimp [Δ,δLoss,t] at *
    nlinarith only [hc,hc2,hccap,hηc,hθsmall,hm,hξ]
end Oberwolfach
