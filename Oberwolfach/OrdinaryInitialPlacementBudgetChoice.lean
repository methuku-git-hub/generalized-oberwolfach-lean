module

public import Oberwolfach.OrdinaryPreSampleForCertificateCap

@[expose] public section
/-! One placement budget satisfies both the first-level certificate's
absolute edit tolerance and its inner-domain edit margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_placement_budget_choice
    (ηedit ζ ε capOriginal:ℝ) (hη:0<ηedit) (hζ:0<ζ) (hε:0<ε) (hcap:0<capOriginal):
    ∃ηBudget capChosen:ℝ,0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζ*ε/2 ∧
      0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηBudget :=by
  let ηBudget:=min ηedit (ζ*ε/100)
  let capChosen:=min capOriginal ηBudget
  have hBudget:0<ηBudget:=by dsimp [ηBudget]; positivity
  have hηBudget:ηBudget≤ηedit:=min_le_left _ _
  have hscale:ηBudget≤ζ*ε/100:=min_le_right _ _
  have hproduct:0<ζ*ε:=mul_pos hζ hε
  have hsmall:15*ηBudget≤ζ*ε/2:=by nlinarith [hscale]
  have hChosen:0<capChosen:=by dsimp [capChosen]; positivity
  exact ⟨ηBudget,capChosen,hBudget,hηBudget,hsmall,hChosen,min_le_left _ _,min_le_right _ _⟩
end Oberwolfach
