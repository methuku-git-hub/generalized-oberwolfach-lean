module

public import Oberwolfach.FirstVortexParentCoefficientAlignment
public import Oberwolfach.FirstVortexParentConfigurationAlignment

@[expose] public section
/-! Align the level theorem's conservative parent margins with the actual
selector coefficients and its smaller parent/deeper-balance event rates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_actual_parent_tolerance_alignment
    (r:ℕ) (ρ₀ sstar tstar B δ ζCfg κ x thetaDeep eta ε etaBal cap₁ cap₂ βA cycleCoeff pathCoeff:ℝ)
    (hρ₀:0<ρ₀) (hs:0<sstar) (ht:0<tstar) (htsmall:tstar≤sstar/(((r+4):ℕ):ℝ)) (hB:0≤B)
    (hδ:0<δ) (hx:0<x) (hEtaBal:0<etaBal) (hε:0<ε) (hc₁:0<cap₁) (hc₂:0<cap₂)
    (hCfg:δ≤ζCfg)
    (hcycle:3*βA≤cycleCoeff-((r+5:ℕ):ℝ)*ζCfg)
    (hpath:3*βA≤pathCoeff-((r+4:ℕ):ℝ)*ζCfg):
    let m:ℝ:=((r+4):ℕ)
    let pLevel:=ρ₀*tstar/2
    let pSelector:=ρ₀*sstar/(2*m)
    let CpLevel:=11*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let CpSelector:=11*(m+1)^4*(2*B/pSelector^(2*(r+4)+1))
    let ClLevel:=5*(m+1)^4*(2*B/pLevel^(2*(r+4)+1))
    let ClSelector:=5*(m+1)^4*(2*B/pSelector^(2*(r+4)+1));
    δ+((r+12:ℕ):ℝ)*δ≤κ/4→δ+((r+12:ℕ):ℝ)*δ≤x/2→
    δ+δ+CpLevel*δ≤κ/4→δ+δ+CpLevel*δ≤thetaDeep/4→
    δ+δ+ClLevel*(4/ε)*δ≤eta/4→δ+δ≤tstar/8→
    ∃δ' εBal ζBal:ℝ,0<δ' ∧ δ'≤δ ∧ 2*δ'≤ζCfg ∧
      δ'≤(κ/2)/4 ∧ δ'+((r+12:ℕ):ℝ)*δ'≤(κ/2)/4 ∧
      δ'+((r+12:ℕ):ℝ)*δ'≤(x/2)/2 ∧
      δ'+δ'+CpSelector*δ'≤(κ/2)/4 ∧ δ'+δ'+CpSelector*δ'≤(thetaDeep/2)/4 ∧
      δ'+δ'+ClSelector*(4/ε)*δ'≤(eta/2)/4 ∧
      δ'+δ'≤tstar/16 ∧ δ'+δ'≤(sstar/m)/8 ∧
      0<εBal ∧ 0<ζBal ∧ εBal≤cap₁ ∧ ζBal≤cap₂ ∧
      εBal+((r+4)+2:ℕ)*ζBal≤etaBal/2 ∧ εBal+((r+4)+2:ℕ)*ζBal≤x/4 ∧
      3*βA≤cycleCoeff-((r+5:ℕ):ℝ)*δ' ∧
      3*βA≤pathCoeff-((r+4:ℕ):ℝ)*δ' :=by
  intro m pLevel pSelector CpLevel CpSelector ClLevel ClSelector hRef hEndpoint hParent hDeep hActive hRow
  obtain ⟨δ',εBal,ζBal,hδ',hδle,hcfg,hδκ,hRef',hEndpoint',hParent',hDeep',hActive',hRow',hspoke,
    he,hz,hecap,hzcap,hbalance,hmargin⟩:=
    first_vortex_parent_level_tolerance_alignment r δ ζCfg κ x thetaDeep eta tstar (sstar/m) CpLevel ClLevel ε etaBal cap₁ cap₂
      hδ hx hEtaBal hc₁ hc₂ hCfg htsmall hRef hEndpoint hParent hDeep hActive hRow
  obtain ⟨_,_,hCp,_,hCl⟩:=first_vortex_parent_coefficient_alignment r ρ₀ sstar tstar B δ' ε hρ₀ hs ht htsmall hB hδ'.le hε
  obtain ⟨hcycle',hpath',_,_,_⟩:=first_vortex_parent_configuration_alignment r βA cycleCoeff pathCoeff ζCfg δ' hδ'.le hcfg hcycle hpath
  refine ⟨δ',εBal,ζBal,hδ',hδle,hcfg,hδκ,hRef',hEndpoint',?_,?_,?_,hRow',hspoke,he,hz,hecap,hzcap,hbalance,hmargin,hcycle',hpath'⟩ <;> linarith
end Oberwolfach
