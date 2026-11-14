module

public import Oberwolfach.OrdinaryVortexGeometryCostBalanceThresholdPayload
public import Oberwolfach.OrdinaryThreeStepBalanceThresholdPayload
public import Oberwolfach.OrdinaryLookbackVortexThresholdPayload

@[expose] public section
/-! One beta-dependent payload retains the local certificate, uniform
geometry, selected costs, arbitrary-lookback balance and actual vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

def OrdinaryVortexGeometryCostWithBalancePayload
    (mWheel loadK d k:ℕ) (hd:2≤d) (ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout cap costRate χthree β:ℝ)
    (Payload:ℝ→ℕ→ℕ→Prop) (m₀ Nmin:ℕ):Prop :=
    ∃mCombined mBalance:ℕ,mCombined≤m₀ ∧ mBalance≤m₀ ∧
      OrdinaryVortexGeometryCostPayload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
        βparent b B εparent gap βout ζout ηpack εout cap costRate β Payload mCombined Nmin ∧
      OrdinaryThreeStepBalanceProductAt d hd εR εH β ε ρ₀ χthree mBalance

theorem ordinary_vortex_all_threshold_payload
    (mWheel loadK d k:ℕ) (hd:2≤d) (ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout βcap δInitial δDeep δedit:ℝ)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hξ:0≤ξroot) (hεR:0<εR) (hεH:0<εH)
    (hgeometry:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh 1 εR εH
        βparent b B εparent gap βout ζout ηpack εout)
    (cap costRate χthree:ℝ) (hcost:OrdinarySelectedCostRate ε ρ₀ cap d costRate) (hχ:0<χthree)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,∃mCombined mVortex:ℕ,mCombined≤m₀ ∧ mVortex≤m₀ ∧
        OrdinaryVortexGeometryCostWithBalancePayload mWheel loadK d k hd ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
          βparent b B εparent gap βout ζout ηpack εout cap costRate χthree β Payload mCombined Nmin ∧
        OrdinaryLookbackVortexAt β ε ρ₀ d mVortex :=by
  let GeometryCost:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>
    OrdinaryVortexGeometryCostPayload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout cap costRate β Payload m₀ Nmin
  have hGeometryCost:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,GeometryCost β m₀ Nmin:=
    ordinary_vortex_uniform_geometry_cost_threshold_payload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout βcap δInitial δDeep δedit hρ₀ hξ hεR.le hεH.le hgeometry cap costRate hcost Payload hPayload
  let WithBalance:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>
    OrdinaryVortexGeometryCostWithBalancePayload mWheel loadK d k hd ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout cap costRate χthree β Payload m₀ Nmin
  have hWithBalance:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,WithBalance β m₀ Nmin:=
    ordinary_three_step_balance_threshold_payload d hd εR εH ε ρ₀ χthree βcap δInitial δDeep δedit
      hεR hεH hε hε1 hρ₀ hχ GeometryCost hGeometryCost
  exact ordinary_lookback_vortex_threshold_payload d ε ρ₀ βcap δInitial δDeep δedit hε hε1 hρ₀ WithBalance hWithBalance
end Oberwolfach
