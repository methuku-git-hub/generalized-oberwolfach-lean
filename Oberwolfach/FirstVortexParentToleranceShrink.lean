module

public import Mathlib.Tactic

@[expose] public section
/-! Shrink the later parent-event tolerance while retaining the earlier
configuration tolerance.  This creates the half-margins needed by the active
and deeper level records. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_parent_tolerance_shrink
    (r:ℕ) (δ ζCfg κ x thetaDeep eta tstar Cp Cl ε:ℝ)
    (hδ:0<δ) (hCfg:δ≤ζCfg)
    (hRef:δ+((r+12:ℕ):ℝ)*δ≤κ/4)
    (hEndpoint:δ+((r+12:ℕ):ℝ)*δ≤x/2)
    (hParent:δ+δ+Cp*δ≤κ/4)
    (hDeep:δ+δ+Cp*δ≤thetaDeep/4)
    (hActive:δ+δ+Cl*(4/ε)*δ≤eta/4)
    (hRow:δ+δ≤tstar/8):
    ∃δ':ℝ,0<δ' ∧ δ'≤δ ∧ 2*δ'≤ζCfg ∧
      δ'+((r+12:ℕ):ℝ)*δ'≤κ/8 ∧
      δ'+((r+12:ℕ):ℝ)*δ'≤x/4 ∧
      δ'+δ'+Cp*δ'≤κ/8 ∧
      δ'+δ'+Cp*δ'≤thetaDeep/8 ∧
      δ'+δ'+Cl*(4/ε)*δ'≤eta/8 ∧
      δ'+δ'≤tstar/16 :=by
  let δ':ℝ:=δ/2
  have hδ':0<δ':=by dsimp [δ'];positivity
  refine ⟨δ',hδ',?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> dsimp [δ'] <;> nlinarith
end Oberwolfach
