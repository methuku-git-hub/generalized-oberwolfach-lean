module

public import Oberwolfach.OrdinaryTriangleOriginalPreVortexCaps
public import Oberwolfach.OrdinaryTriangleCorrectionPresampleBeforeEditCap
public import Oberwolfach.OrdinaryTriangleVortexReferenceSelectionAt

@[expose] public section
/-! From the original feasible triangle parameters, select correction,
matching, reference and vortex data in their pre-host order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_original_ordered_early_setup
    (L:ℕ) (θ α₀ εmax ρ₀ βfreq:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1)
    (hα₀:0<α₀) (hεmax:0<εmax) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1)
    (hβfreq:0<βfreq) (hβfreq1:βfreq≤1):
    let pstar:=ρ₀*(βfreq/200)/2;
    ∃hpstar:0<pstar, pstar≤1 ∧
    ∃α cInner CInner κ cOuter COuter hrefLocal δcut ζcut εcut ζlimit εsample εvortex cBoundary cInitial εcap eParent hParent:ℝ,
      ∃hα:0<α, α≤α₀ ∧ α≤1 ∧ max (1/2) (cycleThreshold 3)+α/4≤1 ∧
      0<cInner ∧ 0<CInner ∧ OrdinaryNamedTriangleInnerEndpointSelector (α/2) cInner CInner ∧
      OrdinaryTriangleOriginalRootFreeCoherentActualAtMargin pstar (ρ₀/8) α cInner CInner ρ₀ pstar (1:ℝ) hpstar ∧
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
      0<hParent ∧ hParent≤cBoundary ∧ hParent≤cInitial ∧
    ∃δAbs hAbs εabs εv capInner:ℝ,
      OrdinaryWeightedCorrectionAfterEarly 3 (α/2) pstar (ρ₀/4) δAbs hAbs εabs εv ∧
      0<capInner ∧ capInner≤εcap ∧ capInner≤εabs ∧ capInner≤εv ∧
    ∃m k:ℕ,∃βPlace lamPlace ζPlace εearly:ℝ,∃dMin:ℕ,
      0<εearly ∧ εearly≤capInner ∧
      OrdinaryOriginalThresholdFamilyAt L 3 βfreq ρ₀ α (by omega) hβfreq hβfreq1 hρ₀ hα m k ∧
      OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin ∧
      (∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleAtEarly L 3 d m k dMin βfreq ρ₀ α (α/2) capInner capEdit θ
          (by omega) hβfreq hβfreq1 hρ₀ hα βPlace lamPlace ζPlace εearly) ∧
      OrdinaryTriangleVortexReferenceSelectionAt pstar (ρ₀/8) α cInner CInner ρ₀ pstar (1:ℝ) hpstar
        εearly eParent hParent 1 :=by
  intro pstar
  obtain ⟨hpstar,hpstar1,α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,εcap,eParent,hParent,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum,hBoundary,hInitial,hdeep,hmatch,
    hεcap,hεmax',hεvortex,hεκ,hερ,he,heB,heI,hh,hhB,hhI⟩:=
      ordinary_triangle_original_pre_vortex_caps θ α₀ εmax ρ₀ βfreq 1 hθhalf hθcycle hθ1 hα₀ hεmax hρ₀ hρ₀1 hβfreq hβfreq1 (by norm_num)
  obtain ⟨δAbs,hAbs,εabs,εv,capInner,hCorr,hInner,hMax,hAbsCap,hV,m,k,βPlace,lamPlace,ζPlace,εearly,dMin,
    hearly,hearlyCap,hAt,hEarly,hTail⟩:=
      ordinary_triangle_correction_presample_before_edit_cap L βfreq ρ₀ α εcap θ hβfreq hβfreq1 hρ₀ hρ₀1 hα hεcap hθhalf
  have hReference:=ordinary_triangle_vortex_reference_selection_at pstar (ρ₀/8) α cInner CInner ρ₀ pstar 1 hpstar hroot
    εearly eParent hParent 1 hearly he hh (by norm_num)
  exact ⟨hpstar,hpstar1,α,cInner,CInner,κ,cOuter,COuter,hrefLocal,δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,cInitial,εcap,eParent,hParent,
    hα,hαsub,hα1,hmargin,hc,hC,hinner,hroot,hκ,hκ1,hκcap,hcOuter,hCOuter,houter,
    hhref,hhrefcap,hδ,hδsmall,hδcap,hζcut,hεcut,hζlimit,hεsample,hεv,hεvsmall,hnum,hBoundary,hInitial,hdeep,hmatch,
    hεcap,hεmax',hεvortex,hεκ,hερ,he,heB,heI,hh,hhB,hhI,
    δAbs,hAbs,εabs,εv,capInner,hCorr,hInner,hMax,hAbsCap,hV,m,k,βPlace,lamPlace,ζPlace,εearly,dMin,
    hearly,hearlyCap,hAt,hEarly,hTail,hReference⟩
end Oberwolfach
