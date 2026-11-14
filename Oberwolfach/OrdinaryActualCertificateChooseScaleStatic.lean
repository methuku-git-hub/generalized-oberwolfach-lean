module

public import Oberwolfach.OrdinaryActualCertificateAfterScaleStaticAt
public import Oberwolfach.OrdinaryActualCertificateAfterHubStaticAt
public import Oberwolfach.OrdinaryVortexScaleBeforeFailure

@[expose] public section
/-! Choose the certificate's vortex scale below the original, placement,
absorber and deep-event bounds before fixing any failure allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_certificate_choose_scale_static
    (mWheel loadK k:ℕ) (hm:3≤mWheel) (α βparent ω bRoot BRoot hpack δ εstar cLinear:ℝ)
    (ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap:ℝ)
    (δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit:ℝ)
    (γ bHub BHub p₀ κ ηhub ζhub aEnd ηend ζlocal δend:ℝ)
    (hafter:OrdinaryActualCertificateAfterHubStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
      ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
      δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
      γ bHub BHub p₀ κ ηhub ζhub aEnd ηend ζlocal δend)
    (root eParent hParent εmax εearly capInner:ℝ)
    (hroot:0<root) (he:0<eParent) (hh:0<hParent) (hγe:γ≤eParent)
    (heB:eParent≤cBoundary) (hhB:hParent≤cBoundary) (heI:eParent≤cInitial) (hhI:hParent≤cInitial)
    (hmax:0<εmax) (hearly:0<εearly) (hinner:0<capInner) (hη:0<ηhub) (ha:0<a) (hρ:0<ρ₀):
    ∃εcap:ℝ,0<εcap ∧ εcap≤εmax ∧ εcap≤εearly ∧ εcap≤capInner ∧ εcap≤ηhub ∧ εcap≤a ∧ εcap≤ρ₀/16 ∧
    ∃cMatch eCleanup hCleanup lam ε βe βh θmatch:ℝ,
      0<cMatch ∧ eCleanup=eParent/2 ∧ hCleanup=hParent/2 ∧
      cMatch≤min (ζhub*γ*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2 ∧
      βe=eCleanup*ε ∧ βh=hCleanup*ε ∧ 0<βe ∧ 0<βh ∧
      0<lam ∧ lam≤root ∧ lam≤1/4 ∧ lam≤(ρ₀/8)/2 ∧ lam≤βe/4 ∧ lam≤βh/2 ∧
      3*(((loadK:ℝ)+1)*lam)≤edit/4 ∧ lam*((mWheel:ℝ)+1)≤edit/4 ∧
      0<ε ∧ ε≤εcap ∧ ε≤εvortex ∧ ε<1/4 ∧ ε≤ξreserve/2 ∧ ε≤ξreserve*(ρ₀/8)/2 ∧ 2*ε^2≤lam ∧
      θmatch=cMatch*ε ∧ 0<θmatch ∧
      OrdinaryActualCertificateAfterScaleStaticAt mWheel loadK k hm α βparent ω bRoot BRoot hpack δ εstar cLinear
        ρ₀ hmin href a ρ θ pmin ηProfile b B εparent gap
        δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial βout ξreserve ζout edit
        γ bHub BHub p₀ κ ηhub ζhub ζlocal δend eParent hParent lam ε βe βh θmatch :=by
  obtain ⟨εcap,hεcap,hmax',hearly',hinner',hη',ha',hρ'⟩:=
    ordinary_vortex_scale_before_failure εmax εearly capInner ηhub a ρ₀ hmax hearly hinner hη ha hρ
  exact ⟨εcap,hεcap,hmax',hearly',hinner',hη',ha',hρ',
    hafter root eParent hParent εcap hroot he hh hεcap hγe heB hhB heI hhI⟩
end Oberwolfach
