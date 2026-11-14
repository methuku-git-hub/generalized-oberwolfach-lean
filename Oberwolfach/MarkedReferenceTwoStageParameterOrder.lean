module

public import Oberwolfach.MarkedReferenceTwoStageInputs

@[expose] public section
/-! Choose the configuration parameter before applying the two-stage
packing theorem and the later error tolerance afterwards. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_reference_choose_two_stage_configuration_parameter
    (betaA t:ℝ) (hbetaA:0<betaA) (ht:0<t):
    ∃ beta:ℝ,0<beta∧beta≤t/2∧2*beta≤3*(min betaA (t/4)):=by
  let beta:=min (betaA/4) (t/8)
  have hb:0<beta:=by dsimp [beta];positivity
  have hbA:beta≤betaA/4:=min_le_left _ _
  have hbt:beta≤t/8:=min_le_right _ _
  refine ⟨beta,hb,?_,?_⟩
  · linarith
  · by_cases h:betaA≤t/4
    · rw [min_eq_left h];linarith
    · rw [min_eq_right (le_of_not_ge h)];linarith

theorem marked_reference_choose_two_stage_error
    (eps₁ eps₂ theta:ℝ) (h₁:0<eps₁) (h₂:0<eps₂) (hθ:0<theta):
    ∃ kappa thetaDeep:ℝ,0<kappa∧0<thetaDeep∧kappa≤eps₂∧
      kappa/4≤min eps₁ eps₂∧thetaDeep/4≤theta/2:=by
  let kappa:=min eps₁ eps₂
  let thetaDeep:=theta
  have hk:0<kappa:=by dsimp [kappa];positivity
  refine ⟨kappa,thetaDeep,hk,hθ,min_le_right _ _,?_,?_⟩ <;> linarith
end Oberwolfach
