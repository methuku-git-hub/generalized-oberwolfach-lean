module

public import Oberwolfach.LongParentMatchingFailureBudget

@[expose] public section
/-! Once a positive extra-event budget has been fixed early, the remaining
failure probabilities can be chosen later without exhausting the gap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_early_extra_failure_budget_choice
    (ε₀ εExtra cap:ℝ) (hε₀:0<ε₀) (hεExtra:0<εExtra)
    (hcapExtra:4*εExtra≤ε₀) (hcap:0<cap):
    ∃ χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ χ≤cap ∧ 0<χCommon ∧ χCommon≤cap ∧
      0<χBal ∧ χBal≤cap ∧ 0<χNbr ∧ χNbr≤cap ∧
      0<χLoad ∧ χLoad≤cap ∧ 0<χLocal ∧ χLocal≤cap ∧
      0<χConfig ∧ χConfig≤cap ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ := by
  let δ:=min cap (ε₀/20)
  have hd:0<δ:=by dsimp [δ];positivity
  have hdc:δ≤cap:=min_le_left _ _
  have hde:δ≤ε₀/20:=min_le_right _ _
  refine ⟨δ,δ,δ,δ,δ,δ,δ,hd,hdc,hd,hdc,hd,hdc,hd,hdc,hd,hdc,hd,hdc,hd,hdc,?_⟩
  linarith
end Oberwolfach
