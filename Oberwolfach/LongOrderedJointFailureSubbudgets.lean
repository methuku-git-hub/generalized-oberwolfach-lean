module

public import Oberwolfach.LongOrderedJointFailureBudget

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_ordered_joint_failure_subbudgets (χ:ℝ) (hχ:0<χ):
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧
      6*(ε₀+6*ηEvent)≤χ ∧ 6*(ε₀+6*ηEvent)<1 ∧
      ∀εExtra:ℝ,4*εExtra≤ε₀→
        ∃χ₁ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
          0<χ₁ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
          χ₁+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig+εExtra<ε₀ := by
  obtain ⟨ε₀,ηEvent,hε,hε1,hη,hχbudget,hpositive⟩:=long_ordered_joint_failure_budget χ hχ
  refine ⟨ε₀,ηEvent,hε,hε1,hη,hχbudget,hpositive,?_⟩
  intro εExtra hExtra
  refine ⟨ε₀/32,ε₀/32,ε₀/32,ε₀/32,ε₀/32,ε₀/32,ε₀/32,
    by positivity,by positivity,by positivity,by positivity,by positivity,by positivity,by positivity,?_⟩
  linarith
end Oberwolfach
