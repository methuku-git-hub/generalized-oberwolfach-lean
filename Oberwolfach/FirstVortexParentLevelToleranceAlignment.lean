module

public import Oberwolfach.FirstVortexParentBalanceToleranceChoices

@[expose] public section
/-! Instantiate the old level tolerances as halves of the new level scales,
using one shrunken parent-event tolerance and one deeper-balance pair. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_parent_level_tolerance_alignment
    (r:ℕ) (δ ζCfg κ x thetaDeep eta tstar spokeRate Cp Cl ε etaBal cap₁ cap₂:ℝ)
    (hδ:0<δ) (hx:0<x) (hEtaBal:0<etaBal) (hc₁:0<cap₁) (hc₂:0<cap₂)
    (hCfg:δ≤ζCfg) (hspoke:tstar≤spokeRate)
    (hRef:δ+((r+12:ℕ):ℝ)*δ≤κ/4)
    (hEndpoint:δ+((r+12:ℕ):ℝ)*δ≤x/2)
    (hParent:δ+δ+Cp*δ≤κ/4)
    (hDeep:δ+δ+Cp*δ≤thetaDeep/4)
    (hActive:δ+δ+Cl*(4/ε)*δ≤eta/4)
    (hRow:δ+δ≤tstar/8):
    ∃δ' εBal ζBal:ℝ,0<δ' ∧ δ'≤δ ∧ 2*δ'≤ζCfg ∧
      δ'≤(κ/2)/4 ∧ δ'+((r+12:ℕ):ℝ)*δ'≤(κ/2)/4 ∧
      δ'+((r+12:ℕ):ℝ)*δ'≤(x/2)/2 ∧
      δ'+δ'+Cp*δ'≤(κ/2)/4 ∧ δ'+δ'+Cp*δ'≤(thetaDeep/2)/4 ∧
      δ'+δ'+Cl*(4/ε)*δ'≤(eta/2)/4 ∧
      δ'+δ'≤tstar/16 ∧ δ'+δ'≤spokeRate/8 ∧
      0<εBal ∧ 0<ζBal ∧ εBal≤cap₁ ∧ ζBal≤cap₂ ∧
      εBal+((r+4)+2:ℕ)*ζBal≤etaBal/2 ∧
      εBal+((r+4)+2:ℕ)*ζBal≤x/4 :=by
  obtain ⟨δ',εBal,ζBal,hδ',hδle,hcfg,hRef',hEndpoint',hParent',hDeep',hActive',hRow',
    he,hz,hecap,hzcap,hbalance,hmargin⟩:=
    first_vortex_parent_balance_tolerance_choices r δ ζCfg κ x thetaDeep eta tstar Cp Cl ε etaBal cap₁ cap₂
      hδ hx hEtaBal hc₁ hc₂ hCfg hRef hEndpoint hParent hDeep hActive hRow
  have hr:0≤((r+12:ℕ):ℝ):=by positivity
  have hδκ:δ'≤κ/8:=by nlinarith [mul_nonneg hr hδ'.le]
  refine ⟨δ',εBal,ζBal,hδ',hδle,hcfg,?_,?_,?_,?_,?_,?_,hRow',?_,
    he,hz,hecap,hzcap,hbalance,hmargin⟩ <;> linarith
end Oberwolfach
