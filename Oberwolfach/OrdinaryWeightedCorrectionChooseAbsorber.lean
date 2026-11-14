module

public import Oberwolfach.OrdinaryWeightedCorrectionAfterAbsorberChoices

@[expose] public section
/-! Instantiate the correction theorem at the matching spacing while
retaining its later terminal and same-sample probability quantifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_weighted_correction_choose_absorber
    (r d:ℕ) (hd:2 ≤ d) (mAbs:ℕ) (α pstar ω δ h εabs εv L ξ:ℝ)
    (hCorr:OrdinaryWeightedCorrectionAfterEarly r α pstar ω δ h εabs εv)
    (hL:0 ≤ L) (hξ:0<ξ) (hξh:ξ ≤ h/100):
    ∃a b:ℕ,OrdinaryWeightedCorrectionAfterAbsorberChoices r d hd mAbs a b α pstar ω εabs εv L ξ :=by
  obtain ⟨hδ,hδsmall,hh,hεabs,hεv,hselect⟩:=hCorr
  exact hselect d hd L hL ξ hξ hξh mAbs
end Oberwolfach
