module

public import Oberwolfach.OrdinaryDeepReserveGeometryParameterChoice
public import Oberwolfach.OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale

@[expose] public section
/-! The quantitative geometry callback admits a vortex scale selected before
the packing error; the later root-size parameter is then chosen compatibly. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_buffered_geometry_before_vortex_scale
    (mWheel k r:ℕ) (ρ₀ βparent b B εparent gap ξ ζ pReserve cGeom:ℝ)
    (p a bEdge bHub cap₀ cLinear:ℝ)
    (hρ₀:0<ρ₀) (hξ:0<ξ) (hGeom:0<cGeom)
    (hp:0<p) (ha:0<a) (hbe:0<bEdge) (hbh:0<bHub) (hcap:0<cap₀) (hLinear:0<cLinear)
    (hgeo:∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧ cGeom*min 1 η≤γ ∧
      OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale mWheel k 3 ρ₀ βparent b B εparent gap η
        (βparent/2) ξ ζ pReserve eps γ):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η:ℝ,0<η→
      cLinear*ordinarySafeCleanupScale r p (a*ε) (bEdge*ε) (bHub*ε) (cap₀*ε^2)≤η→
    ∃eps γ lam:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧ cGeom*min 1 η≤γ ∧
      OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale mWheel k 3 ρ₀ βparent b B εparent gap η
        (βparent/2) ξ ζ pReserve eps γ ∧
      0≤lam ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤γ/(1000*((mWheel:ℝ)+2)) ∧
      ε≤ξ/2 ∧ ε≤ξ*(ρ₀/8)/2 ∧ 2*ε^3≤lam :=by
  obtain ⟨εcap,hεcap,hεcap1,hchoice⟩:=ordinary_deep_reserve_geometry_parameter_choice r mWheel p a bEdge bHub cap₀ cLinear cGeom ξ ρ₀
    hp ha hbe hbh hcap hLinear hGeom hξ hρ₀
  refine ⟨εcap,hεcap,hεcap1,?_⟩
  intro ε hε hεcap' η hη hpack
  obtain ⟨eps,γ,heps,heps1,hγ,hγlower,hgeometry⟩:=hgeo η hη
  obtain ⟨lam,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot⟩:=hchoice ε hε hεcap' η γ hpack hγlower
  exact ⟨eps,γ,lam,heps,heps1,hγ,hγlower,hgeometry,hlam,hlam1,hlamρ,hlamγ,hεξ,hερ,hεroot⟩
end Oberwolfach
