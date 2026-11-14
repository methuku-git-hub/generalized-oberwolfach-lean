module

public import Oberwolfach.LongOrderedJointFailureSubbudgets

@[expose] public section
/-! The structural selector's combined failure allowance can be made
arbitrarily small while retaining its seven positive subbudgets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_selector_common_failure_choice_arbitrary (χ:ℝ) (hχ:0<χ):
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧
      0<1-(36*(ε₀+6*ηEvent)+ηEvent) ∧
      36*(ε₀+6*ηEvent)+ηEvent≤χ ∧
    ∀εExtra:ℝ,4*εExtra≤ε₀→
    ∃χ₁ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ₁ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
      χ₁+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀:=by
  let c:=min (χ/7) (1/200:ℝ)
  have hc:0<c:=by dsimp [c];positivity
  have hcχ:c≤χ/7:=min_le_left _ _
  have hcsmall:c≤1/200:=min_le_right _ _
  obtain ⟨ε₀,ηEvent,hε,hε1,hη,hbudget,_hsmall,hchoose⟩:=
    long_ordered_joint_failure_subbudgets c hc
  have hχbudget:36*(ε₀+6*ηEvent)+ηEvent≤χ:=by linarith
  have hpositive:0<1-(36*(ε₀+6*ηEvent)+ηEvent):=by linarith
  exact ⟨ε₀,ηEvent,hε,hε1,hη,hpositive,hχbudget,hchoose⟩
end Oberwolfach
