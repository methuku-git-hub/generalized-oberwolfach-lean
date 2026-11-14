module

public import Oberwolfach.OrdinaryVortexUniformGeometryThresholdPayload
public import Oberwolfach.OrdinarySelectedCostJoinThresholdPayload

@[expose] public section
/-! Keep a spoke-uniform geometry threshold together with later certificate
thresholds before the terminal vortex size is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_uniform_geometry_cost_threshold_payload
    (mWheel loadK d k:ℕ) (ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout βcap δInitial δDeep δedit:ℝ)
    (hρ₀:0<ρ₀) (hξ:0≤ξroot) (hεR:0≤εR) (hεH:0≤εH)
    (hgeometry:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh 1 εR εH
        βparent b B εparent gap βout ζout ηpack εout)
    (cap costRate:ℝ) (hcost:OrdinarySelectedCostRate ε ρ₀ cap d costRate)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,∃mGeoPayload mCost:ℕ,mGeoPayload≤m₀ ∧ mCost≤m₀ ∧
        (∃mCert mGeom:ℕ,mCert≤mGeoPayload ∧ mGeom≤mGeoPayload ∧ Payload β mCert Nmin ∧
          (∀pH:ℝ,0≤pH→pH≤1→
            OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k mGeom β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH
              βparent b B εparent gap βout ζout ηpack εout)) ∧
        OrdinarySelectedCostAtSpacing ε ρ₀ cap d costRate β mCost :=by
  let GeoPayload:ℝ→ℕ→ℕ→Prop:=fun β m₀ Nmin=>
    ∃mCert mGeom:ℕ,mCert≤m₀ ∧ mGeom≤m₀ ∧ Payload β mCert Nmin ∧
      (∀pH:ℝ,0≤pH→pH≤1→
        OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k mGeom β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH
          βparent b B εparent gap βout ζout ηpack εout)
  have hGeo:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,GeoPayload β m₀ Nmin:=
    ordinary_vortex_uniform_geometry_threshold_payload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout βcap δInitial δDeep δedit hρ₀ hξ hεR hεH hgeometry Payload hPayload
  exact ordinary_selected_cost_join_threshold_payload ε ρ₀ cap d costRate βcap δInitial δDeep δedit hcost GeoPayload hGeo
end Oberwolfach
