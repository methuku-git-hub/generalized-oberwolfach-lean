module

public import Oberwolfach.OrdinaryVortexSharpGeometryUniformSpokeRate

@[expose] public section
/-! Keep a spoke-uniform geometry threshold together with later certificate
thresholds before the terminal vortex size is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_uniform_geometry_threshold_payload
    (mWheel loadK d k:ℕ) (ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout βcap δInitial δDeep δedit:ℝ)
    (hρ₀:0<ρ₀) (hξ:0≤ξroot) (hεR:0≤εR) (hεH:0≤εH)
    (hgeometry:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh 1 εR εH
        βparent b B εparent gap βout ζout ηpack εout)
    (Payload:ℝ→ℕ→ℕ→Prop)
    (hPayload:∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→∃m₀ Nmin:ℕ,Payload β m₀ Nmin):
    ∀β:ℝ,0<β→β≤1/4→β≤βcap→β≤δInitial→β≤δDeep→β≤δedit→
      ∃m₀ Nmin:ℕ,∃mCert mGeom:ℕ,mCert≤m₀ ∧ mGeom≤m₀ ∧ Payload β mCert Nmin ∧
        (∀pH:ℝ,0≤pH→pH≤1→
          OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k mGeom β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH
            βparent b B εparent gap βout ζout ηpack εout) :=by
  intro β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mCert,Nmin,hcert⟩:=hPayload β hβ hβ1 hβcap hInitial hDeep hEdit
  obtain ⟨mGeom,_,hgeom⟩:=ordinary_vortex_sharp_geometry_uniform_spoke_rate mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
    βparent b B εparent gap βout ζout ηpack εout hρ₀ hβ.le hξ hεR hεH (hgeometry β hβ hβ1 hβcap hInitial hDeep hEdit)
  exact ⟨max mCert mGeom,Nmin,mCert,mGeom,le_max_left _ _,le_max_right _ _,hcert,hgeom⟩
end Oberwolfach
