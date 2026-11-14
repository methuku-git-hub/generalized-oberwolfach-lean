module

public import Oberwolfach.OrdinaryWeightedCorrectionChooseAbsorber

@[expose] public section
/-! The correction rate can be chosen below a later positive cap while
remaining fixed before the absorber size and its finite choices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_correction_rate_before_absorber_under_cap
    (r d:ℕ) (hd:2≤d) (α pstar ω δ h εabs εv L cap:ℝ)
    (hcorr:OrdinaryWeightedCorrectionAfterEarly r α pstar ω δ h εabs εv)
    (hL:0≤L) (hcap:0<cap):
    ∃ξ:ℝ,0<ξ ∧ ξ≤cap ∧ ξ≤h/100 ∧
      ∀mAbs:ℕ,∃a b:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices r d hd mAbs a b α pstar ω εabs εv L ξ :=by
  have hh:0<h:=hcorr.2.2.1
  let ξ:=min cap (h/100)
  have hξ:0<ξ:=by dsimp [ξ]; positivity
  have hξcap:ξ≤cap:=min_le_left _ _
  have hξh:ξ≤h/100:=min_le_right _ _
  refine ⟨ξ,hξ,hξcap,hξh,?_⟩
  intro mAbs
  exact ordinary_weighted_correction_choose_absorber r d hd mAbs α pstar ω δ h εabs εv L ξ hcorr hL hξ hξh
end Oberwolfach
