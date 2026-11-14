module

public import Oberwolfach.LongAdaptiveVortexDeeperWeightedExtra

@[expose] public section
/-! The parent-event failure budget and all matching failure budgets can be
chosen together below any prescribed positive cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_parent_matching_failure_budget_choice
    (ε₀ cap:ℝ) (hε₀:0<ε₀) (hcap:0<cap):
    ∃ χ χCommon χBal χNbr χLoad χLocal χConfig εExtra:ℝ,
      0<χ ∧ χ≤cap ∧ 0<χCommon ∧ χCommon≤cap ∧
      0<χBal ∧ χBal≤cap ∧ 0<χNbr ∧ χNbr≤cap ∧
      0<χLoad ∧ χLoad≤cap ∧ 0<χLocal ∧ χLocal≤cap ∧
      0<χConfig ∧ χConfig≤cap ∧ 0<εExtra ∧ εExtra≤cap ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ := by
  let δ:=min cap (ε₀/20)
  have hd:0<δ:=by dsimp [δ];positivity
  have hdc:δ≤cap:=min_le_left _ _
  have hde:δ≤ε₀/20:=min_le_right _ _
  refine ⟨δ,δ,δ,δ,δ,δ,δ,δ,hd,hdc,hd,hdc,hd,hdc,hd,hdc,hd,hdc,hd,hdc,hd,hdc,hd,hdc,?_⟩
  linarith
end Oberwolfach
