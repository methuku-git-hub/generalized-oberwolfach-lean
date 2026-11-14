module

public import Oberwolfach.OrdinaryVortexSharpGeometryUniformSpokeRate
public import Oberwolfach.OrdinaryVortexTwoStepSharpGeometryFromRatesGeneralLoad

@[expose] public section
/-! Select the later sharp-geometry threshold before the factor-dependent
spoke rate is known, using the geometry at rate one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_sharp_geometry_from_rates_uniform_spoke
    (mWheel loadK d k:ℕ) (β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH:ℝ)
    (βparent b B εparent gap βout ζout ηpack εout:ℝ)
    (hgeometry:OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (mWheel+1) k 2 ρ₀ βparent b B εparent gap
      βout ξreserve ζout edit p ηpack εout γ)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hγ:0<γ)
    (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
    (hξreserve:0≤ξreserve) (hεξ:ε≤ξreserve/2) (hερ:ε≤ξreserve*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
    (hβe:0≤βe) (hβh:0≤βh) (hp:0≤p)
    (hεR:0≤εR) (hεH:0≤εH) (hξroot:0≤ξroot) (hκ:0≤κ) (hη:0≤ηbal) (hηI:0≤ηInitial)
    (hedit:0<edit) (hβcap:β≤γ/1000) (hRcap:εR≤γ/1000) (hHcap:εH≤γ/1000)
    (hξcap:ξroot≤γ/160000) (hκcap:κ≤γ/1000) (hηcap:ηbal≤γ/1000) (hηIcap:ηInitial≤ηbal)
    (hrow:3*(((loadK:ℝ)+1)*lam)≤edit/4) (hlevel:lam*((mWheel:ℝ)+1)≤edit/4)
    (hκedit:κ≤edit/(72*((mWheel:ℝ)+2))) (hTcap:lam≤βe/4) (hWcap:lam≤βh/2):
    ∃m₀:ℕ,1≤m₀ ∧ ∀pH:ℝ,0≤pH→pH≤1→
      OrdinaryVortexTwoStepSharpGeometryAtFixedThreshold mWheel loadK d k m₀ β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh pH εR εH
        βparent b B εparent gap βout ζout ηpack εout :=by
  have hmax:OrdinaryVortexTwoStepSharpGeometryAtRatesGeneralLoad mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh 1 εR εH
      βparent b B εparent gap βout ζout ηpack εout:=
    ordinary_vortex_two_step_sharp_geometry_from_rates_general_load mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh 1 εR εH
      βparent b B εparent gap βout ζout ηpack εout hgeometry hβ hβ1 hε hε1 hρ₀ hγ hlam hlam1 hlamρ
      hξreserve hεξ hερ hεroot hβe hβh hp (by norm_num) (by norm_num) hεR hεH hξroot hκ hη hηI hedit
      hβcap hRcap hHcap hξcap hκcap hηcap hηIcap hrow hlevel hκedit hTcap hWcap
  exact ordinary_vortex_sharp_geometry_uniform_spoke_rate mWheel loadK d k β ε ρ₀ lam ξreserve ξroot κ ηbal ηInitial γ edit p βe βh εR εH
    βparent b B εparent gap βout ζout ηpack εout hρ₀ hβ hξroot hεR hεH hmax
end Oberwolfach
