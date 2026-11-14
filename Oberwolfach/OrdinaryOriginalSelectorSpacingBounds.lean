module

public import Oberwolfach.OrdinaryOriginalThresholdPlacementSpacing

@[expose] public section
/-! The original selector's spacing and cutoff inequalities, including the
earlier placement and list-spacing requirements. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryOriginalSelectorSpacingBounds
    (rstar m dNeed dMin d K rank:ℕ) (βfreq θ βSel lamSel ζSel smin:ℝ):Prop :=
  0<βSel ∧ βSel ≤ 1 ∧ 0<lamSel ∧ 0<ζSel ∧ 0<smin ∧ smin=βfreq/200 ∧
  dMin ≤ d ∧ dNeed ≤ d ∧ 2 ≤ d ∧ 3 ≤ K ∧ rstar ≤ K ∧ 2 ≤ rank ∧ 2*(m+1) ≤ rank ∧
  (∀i:Fin K,2*(longPaddedSeedExponent i+2) ≤ rank) ∧
  1/θ ≤ (d:ℝ) ∧ 1/(4*(d:ℝ)) ≤ 5*θ^2/256 ∧ 1/(2*(K:ℝ)) ≤ βfreq ∧
  5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ) ≤ θ/2
end Oberwolfach
