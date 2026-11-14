module

public import Oberwolfach.OrdinaryTriangleOriginalEarlyBalanceFineSelection
public import Oberwolfach.OrdinaryTriangleEarlyVortexAndBoundaryCaps

@[expose] public section
/-! On the feasible triangle branch, the original positive parameters
supply the retention lower bound and all early vortex and boundary caps. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_original_pre_vortex_caps
    (θ α₀ εmax ρ₀ βfreq ηP:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1)
    (hα₀:0<α₀) (hεmax:0<εmax) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1)
    (hβfreq:0<βfreq) (hβfreq1:βfreq≤1) (hηP:0<ηP):
    let pstar:=ρ₀*(βfreq/200)/2;
    ∃hpstar:0<pstar, pstar≤1 ∧
    ∃α cInner CInner κ cOuter COuter hrefLocal δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial εcap eParent hParent:ℝ,
      0<α ∧ α≤α₀ ∧ α≤1 ∧ max (1/2) (cycleThreshold 3)+α/4≤1 ∧
      0<cInner ∧ 0<CInner ∧ OrdinaryNamedTriangleInnerEndpointSelector (α/2) cInner CInner ∧
      OrdinaryTriangleOriginalRootFreeCoherentActualAtMargin pstar (ρ₀/8) α cInner CInner ρ₀ pstar ηP hpstar ∧
      0<κ ∧ κ≤1 ∧ κ≤ρ₀/8 ∧ 0<cOuter ∧ 0<COuter ∧
      OrdinaryTriangleHubEarlyBeforeFailure (α/2) ρ₀ pstar κ cOuter COuter ∧
      0<hrefLocal ∧ hrefLocal≤(min ((α/2)/4) (1/4:ℝ))*pstar/64 ∧
      0<δcut ∧ δcut<1/4 ∧ δcut≤min ((min ((α/2)/4) (1/4:ℝ))/32) (pstar/512) ∧
      0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
      OrdinaryFixedVortexNonrootNumericAt ρ₀ pstar hrefLocal κ κ κ δcut ζcut εcut ζlimit εsample εvortex ∧
      0<cBoundary ∧ 0<cInitial ∧
      OrdinaryTriangleInitialDeepBalanceSelector ρ₀ (α/2) pstar pstar cBoundary ∧
      OrdinaryTriangleInitialMatchingMarginSelector ρ₀ (α/2) pstar pstar cInitial ∧
      0<εcap ∧ εcap≤εmax ∧ εcap≤εvortex ∧ εcap≤κ ∧ εcap≤ρ₀/16 ∧
      0<eParent ∧ eParent≤cBoundary ∧ eParent≤cInitial ∧
      0<hParent ∧ hParent≤cBoundary ∧ hParent≤cInitial :=by
  intro pstar
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  have hpstar1:pstar≤1:=by
    dsimp [pstar]
    have hh:=mul_nonneg (sub_nonneg.mpr hρ₀1) hβfreq.le
    nlinarith
  obtain ⟨α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum,hBoundary,hInitial,hdeep,hmatch⟩:=
    ordinary_triangle_original_early_balance_fine_selection θ α₀ ρ₀ pstar ηP hθhalf hθcycle hθ1 hα₀ hρ₀ hpstar hpstar1 hηP
  obtain ⟨εcap,eParent,hParent,hεcap,hεmax',hεvortex,hεκ,hερ,he,heB,heI,hh,hhB,hhI⟩:=
    ordinary_triangle_early_vortex_and_boundary_caps εmax εvortex κ ρ₀ cBoundary cInitial
      hεmax hεv hκ hρ₀ hBoundary hInitial
  exact ⟨hpstar,hpstar1,α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,εcap,eParent,hParent,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum,hBoundary,hInitial,hdeep,hmatch,
    hεcap,hεmax',hεvortex,hεκ,hερ,he,heB,heI,hh,hhB,hhI⟩
end Oberwolfach
