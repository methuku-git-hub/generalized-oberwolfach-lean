module

public import Oberwolfach.LongOrderedJointFailureSubbudgets

@[expose] public section
/-! The selector's combined probability and all seven failure budgets can be
chosen before the events, with the correction budget retained afterwards. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_selector_common_failure_choice:
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧
      0<1-(36*(ε₀+6*ηEvent)+ηEvent) ∧
    ∀εExtra:ℝ,4*εExtra≤ε₀→
    ∃χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ :=by
  obtain ⟨ε₀,η,hε,hε1,hη,hsmall,_,hchoices⟩:=
    long_ordered_joint_failure_subbudgets (1/100:ℝ) (by norm_num)
  have hpositive:0<1-(36*(ε₀+6*η)+η):=by nlinarith
  exact ⟨ε₀,η,hε,hε1,hη,hpositive,hchoices⟩
end Oberwolfach
