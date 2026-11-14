module

public import Oberwolfach.OrdinaryInitialPlacementBudgetChoice

@[expose] public section
/-! Choose the matching placement only after the certificate tolerance is
known, retaining the early vortex and list parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_presample_for_initial_placement_budget
    (L rstar m k dMin:ℕ) (βfreq ρ₀ α γList capInner θhost:ℝ)
    (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1) (hρ₀:0<ρ₀) (hα:0<α)
    (βPlace lamPlace ζPlace εearly:ℝ)
    (hTail:∀capEdit:ℝ,0<capEdit→∃d:ℕ,∃hd:2≤d,
      OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capEdit θhost
        hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly)
    (capOriginal ηedit ζ ε:ℝ) (hcap:0<capOriginal) (hη:0<ηedit) (hζ:0<ζ) (hε:0<ε):
    ∃ηBudget capChosen:ℝ,0<ηBudget ∧ ηBudget≤ηedit ∧ 15*ηBudget≤ζ*ε/2 ∧
      0<capChosen ∧ capChosen≤capOriginal ∧ capChosen≤ηBudget ∧
      ∃d:ℕ,∃hd:2≤d,
        OrdinaryOriginalPreSampleAtEarly L rstar d m k dMin βfreq ρ₀ α γList capInner capChosen θhost
          hr hβfreq hβ1 hρ₀ hα βPlace lamPlace ζPlace εearly :=by
  obtain ⟨ηBudget,capChosen,hBudget,hBudgetη,hsmall,hChosen,hOriginal,hCap⟩:=
    ordinary_initial_placement_budget_choice ηedit ζ ε capOriginal hη hζ hε hcap
  exact ⟨ηBudget,capChosen,hBudget,hBudgetη,hsmall,hChosen,hOriginal,hCap,hTail capChosen hChosen⟩
end Oberwolfach
