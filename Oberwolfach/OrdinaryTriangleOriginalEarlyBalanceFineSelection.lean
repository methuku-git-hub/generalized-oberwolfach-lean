module

public import Oberwolfach.OrdinaryTriangleOriginalFineAndRootFreeSelection
public import Oberwolfach.OrdinaryTriangleEarlyBalanceSelectors

@[expose] public section
/-! The original feasible threshold branch supplies the common margin,
distinct inner and outer hub choices, fine-cover caps, and both boundary
selectors before choosing the vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_original_early_balance_fine_selection
    (θ α₀ ρ₀ pstar ηP:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1) (hα₀:0<α₀)
    (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1) (hηP:0<ηP):
    ∃α cInner CInner κ cOuter COuter hrefLocal δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial:ℝ,
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
      OrdinaryTriangleInitialMatchingMarginSelector ρ₀ (α/2) pstar pstar cInitial :=by
  obtain ⟨α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum⟩:=
    ordinary_triangle_original_fine_and_root_free_selection θ α₀ ρ₀ pstar ηP hθhalf hθcycle hθ1 hα₀ hρ₀ hpstar hpstar1 hηP
  obtain ⟨cBoundary,cInitial,hBoundary,hInitial,hdeep,hmatch⟩:=
    ordinary_triangle_early_balance_selectors ρ₀ (α/2) pstar pstar hρ₀ (by positivity) hpstar hpstar
  exact ⟨α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum,hBoundary,hInitial,hdeep,hmatch⟩
end Oberwolfach
