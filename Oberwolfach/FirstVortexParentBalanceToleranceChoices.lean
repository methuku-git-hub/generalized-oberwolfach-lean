module

public import Oberwolfach.FirstVortexParentToleranceShrink
public import Oberwolfach.MarkedVortexInnerBalanceScale

@[expose] public section
/-! The fixed parent configuration, shrunken parent event and later deeper
balance event can use compatible tolerances from one level choice. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_parent_balance_tolerance_choices
    (r:ℕ) (δ ζCfg κ x thetaDeep eta tstar Cp Cl ε etaBal cap₁ cap₂:ℝ)
    (hδ:0<δ) (hx:0<x) (hEtaBal:0<etaBal) (hc₁:0<cap₁) (hc₂:0<cap₂)
    (hCfg:δ≤ζCfg)
    (hRef:δ+((r+12:ℕ):ℝ)*δ≤κ/4)
    (hEndpoint:δ+((r+12:ℕ):ℝ)*δ≤x/2)
    (hParent:δ+δ+Cp*δ≤κ/4)
    (hDeep:δ+δ+Cp*δ≤thetaDeep/4)
    (hActive:δ+δ+Cl*(4/ε)*δ≤eta/4)
    (hRow:δ+δ≤tstar/8):
    ∃δ' εBal ζBal:ℝ,0<δ' ∧ δ'≤δ ∧ 2*δ'≤ζCfg ∧
      δ'+((r+12:ℕ):ℝ)*δ'≤κ/8 ∧ δ'+((r+12:ℕ):ℝ)*δ'≤x/4 ∧
      δ'+δ'+Cp*δ'≤κ/8 ∧ δ'+δ'+Cp*δ'≤thetaDeep/8 ∧
      δ'+δ'+Cl*(4/ε)*δ'≤eta/8 ∧ δ'+δ'≤tstar/16 ∧
      0<εBal ∧ 0<ζBal ∧ εBal≤cap₁ ∧ ζBal≤cap₂ ∧
      εBal+((r+4)+2:ℕ)*ζBal≤etaBal/2 ∧
      εBal+((r+4)+2:ℕ)*ζBal≤x/4 :=by
  obtain ⟨δ',hδ',hδle,hcfg,hRef',hEndpoint',hParent',hDeep',hActive',hRow'⟩:=
    first_vortex_parent_tolerance_shrink r δ ζCfg κ x thetaDeep eta tstar Cp Cl ε
      hδ hCfg hRef hEndpoint hParent hDeep hActive hRow
  let target:=min etaBal (x/2)
  have htarget:0<target:=by dsimp [target];positivity
  obtain ⟨εBal,ζBal,he,hz,hecap,hzcap,hbalance⟩:=
    marked_vortex_inner_balance_error_choices r 1 target cap₁ cap₂ (by norm_num) htarget hc₁ hc₂
  have htargetEta:target≤etaBal:=min_le_left _ _
  have htargetX:target≤x/2:=min_le_right _ _
  refine ⟨δ',εBal,ζBal,hδ',hδle,hcfg,hRef',hEndpoint',hParent',hDeep',hActive',hRow',
    he,hz,hecap,hzcap,?_,?_⟩ <;> nlinarith
end Oberwolfach
