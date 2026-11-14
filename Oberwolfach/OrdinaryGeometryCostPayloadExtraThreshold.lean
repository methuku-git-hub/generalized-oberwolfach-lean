module

public import Oberwolfach.OrdinaryVortexGeometryCostBalanceThresholdPayload

@[expose] public section
/-! The shared geometry and cost payload retains any lower bound built into
its local certificate payload. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_geometry_cost_payload_extra_threshold
    (mWheel loadK d k:ℕ) (ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout cap costRate β:ℝ)
    (Payload:ℝ→ℕ→ℕ→Prop) (m₀ Nmin Nextra:ℕ)
    (hExtra:∀m,Payload β m Nmin→Nextra≤Nmin)
    (h:OrdinaryVortexGeometryCostPayload mWheel loadK d k ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
      βparent b B εparent gap βout ζout ηpack εout cap costRate β Payload m₀ Nmin):
    Nextra≤Nmin :=by
  obtain ⟨mGeo,mCost,hGeo,hCost,⟨mCert,mGeom,hCert,hGeom,hPayload,hGeometry⟩,hSelected⟩:=h
  exact hExtra mCert hPayload
end Oberwolfach
