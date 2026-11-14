module

public import Oberwolfach.LongOrderedJointFailureSubbudgets

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_synchronized_failure_budgets (χ:ℝ) (hχ:0<χ):
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧
      36*(ε₀+6*ηEvent)≤χ ∧ 36*(ε₀+6*ηEvent)<1 ∧
      ∀εExtra:ℝ,4*εExtra≤ε₀→
        ∃χ₁ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
          0<χ₁ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
          χ₁+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ := by
  let χsmall:ℝ:=min χ (1/2)
  have hsmall:0<χsmall:=by dsimp [χsmall];positivity
  obtain ⟨ε₀,ηEvent,hε,hε1,hη,hbudget,_,hsub⟩:=long_ordered_joint_failure_subbudgets (χsmall/6) (by positivity)
  refine ⟨ε₀,ηEvent,hε,hε1,hη,?_,?_,hsub⟩
  · have hh:χsmall≤χ:=min_le_left _ _
    nlinarith
  · have hh:χsmall≤1/2:=min_le_right _ _
    nlinarith
end Oberwolfach
