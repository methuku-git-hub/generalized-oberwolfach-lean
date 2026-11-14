module

public import Oberwolfach.OrdinaryTriangleEarlyBalanceSelectors

@[expose] public section
/-! One early vortex cap and common boundary coefficients satisfy the
selected fine-cover, outer-hub, initial and later balance requirements. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_early_vortex_and_boundary_caps
    (εmax εvortex κ ρ₀ cBoundary cInitial:ℝ)
    (hmax:0<εmax) (hvortex:0<εvortex) (hκ:0<κ) (hρ:0<ρ₀) (hB:0<cBoundary) (hI:0<cInitial):
    ∃εcap eParent hParent:ℝ,0<εcap ∧ εcap≤εmax ∧ εcap≤εvortex ∧ εcap≤κ ∧ εcap≤ρ₀/16 ∧
      0<eParent ∧ eParent≤cBoundary ∧ eParent≤cInitial ∧
      0<hParent ∧ hParent≤cBoundary ∧ hParent≤cInitial :=by
  let εcap:ℝ:=min εmax (min εvortex (min κ (ρ₀/16)))
  let e:ℝ:=min cBoundary cInitial
  have hεcap:0<εcap:=by dsimp [εcap];positivity
  have he:0<e:=by dsimp [e];positivity
  have hmax':εcap≤εmax:=min_le_left _ _
  have hvortex':εcap≤εvortex:=(min_le_right _ _).trans (min_le_left _ _)
  have hκ':εcap≤κ:=((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hρ':εcap≤ρ₀/16:=((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  exact ⟨εcap,e,e,hεcap,hmax',hvortex',hκ',hρ',he,min_le_left _ _,min_le_right _ _,he,min_le_left _ _,min_le_right _ _⟩
end Oberwolfach
