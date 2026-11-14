module

public import Oberwolfach.OrdinaryInitialFineCoverFromSharedAt
public import Oberwolfach.OrdinaryInitialNumericFromShared

@[expose] public section
/-! The shared before-spacing numeric choices provide the initial fine
cover for any balanced edited host with the sampled profile and tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_fine_cover_from_shared_named
    (mWheel loadK d:ℕ) (hm:3≤mWheel)
    (ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ε ξroot aLoad ηbal αcut pstar:ℝ)
    (hnum:OrdinaryFixedVortexNonrootNumericAt ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex)
    (hρ₀:0<ρ₀) (hε:0<ε) (hεv:ε≤εvortex) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (hξ:0<ξroot) (hξε:ξroot≤ε/100) (ha:0<aLoad) (ha1:aLoad≤1) (hξsmall:80*ξroot≤aLoad^2)
    (hbal:0≤ηbal) (hbalcap:ηbal≤δcut*(ρ₀/8)*ξroot/1000)
    (hζcut:0≤ζcut) (hεcut:0≤εcut) (hζlimit:0≤ζlimit)
    (hδlim:δcut≤min (αcut/32) (pstar/512)) (hhref:href≤αcut*pstar/64):
    ∀β:ℝ,0≤β→β≤1/4→∃v₀:ℕ,1≤v₀ ∧
      OrdinaryInitialFineCoverFromSharedAt mWheel loadK d ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample ε ξroot aLoad ηbal αcut pstar β v₀ :=by
  exact ordinary_initial_fine_cover_from_shared_numeric mWheel loadK d hm ρ₀ pmin href a ρ θ δcut ζcut εcut ζlimit εsample εvortex ε ξroot aLoad ηbal αcut pstar
    hnum hρ₀ hε hεv hδ hδsmall hξ hξε ha ha1 hξsmall hbal hbalcap hζcut hεcut hζlimit hδlim hhref
end Oberwolfach
