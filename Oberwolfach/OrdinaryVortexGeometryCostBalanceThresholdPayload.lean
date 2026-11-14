module

public import Oberwolfach.OrdinaryVortexUniformGeometryCostThresholdPayload
public import Oberwolfach.OrdinaryLookbackBalanceThresholdPayload

@[expose] public section
/-! A named size payload combining all local certificate, geometry,
selected-cost and lookback-balance thresholds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

def OrdinaryVortexGeometryCostPayload
    (mWheel loadK d k:ℕ) (ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout cap costRate β:ℝ)
    (Payload:ℝ→ℕ→ℕ→Prop) (m₀ Nmin:ℕ):Prop :=
    ∃mGeoPayload mCost:ℕ,mGeoPayload≤m₀ ∧ mCost≤m₀ ∧
        (∃mCert mGeom:ℕ,mCert≤mGeoPayload ∧ mGeom≤mGeoPayload ∧ Payload β mCert Nmin ∧
          (∀pH:ℝ,0≤pH→pH≤1→
            OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k mGeom β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH
              βparent b B εparent gap βout ζout ηpack εout)) ∧
        OrdinarySelectedCostAtSpacing ε ρ₀ cap d costRate β mCost

theorem ordinary_vortex_geometry_cost_balance_threshold_payload
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
      ∃m₀ Nmin:ℕ,∃mCombined mLook:ℕ,mCombined≤m₀ ∧ mLook≤m₀ ∧
        OrdinaryVortexGeometryCostPayload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
          βparent b B εparent gap βout ζout ηpack εout cap costRate β Payload mCombined Nmin ∧
        OrdinaryLookbackBalanceProductAt d hd εR εH β ε ρ₀ χthree mLook :=by
  let Combined:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>
    OrdinaryVortexGeometryCostPayload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout cap costRate β Payload m₀ Nmin
  have hCombined:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,Combined β m₀ Nmin:=
    ordinary_vortex_uniform_geometry_cost_threshold_payload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout βcap δInitial δDeep δedit hρ₀ hξ hεR.le hεH.le hgeometry cap costRate hcost Payload hPayload
  exact ordinary_lookback_balance_threshold_payload d hd εR εH ε ρ₀ χthree βcap δInitial δDeep δedit
    hεR hεH hε hε1 hρ₀ hχ Combined hCombined
end Oberwolfach
