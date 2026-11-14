module

public import Oberwolfach.OrdinaryLocalDemandBudgetBeforeRates

@[expose] public section
/-! The explicit local-demand expression fits the placement rate when the
inner contraction is chosen first from the proportionality constant. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_assigned_local_expression_before_geometry
    (α cap:ℝ) (hα:0<α) (hcap:0<cap):
    ∃ε:ℝ,0<ε ∧ ε ≤ cap ∧ ∀(n:ℕ) (inner θ b a γ u t edit del LF aux:ℝ),
      0 ≤ inner → 0 ≤ θ → min (α/4096) (1/2:ℝ)*θ ≤ b →
      inner ≤ ε*n → a ≤ b/16 → γ ≤ θ → u ≤ 2*θ → t ≤ θ*inner →
      edit ≤ b*n/16 → aux ≤ b*n/16 → del ≤ b*n/16 → 2*LF ≤ b*n/16 →
      edit+(max (a*n) (γ*inner)+u*inner+3*t+aux+del+LF)+LF ≤ b*n :=by
  let c:ℝ:=min (α/4096) (1/2:ℝ)
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨ε,hε,hεcap,hbudget⟩:=ordinary_local_demand_budget_before_rates c cap hc hcap
  refine ⟨ε,hε,hεcap,?_⟩
  intro n inner θ b a γ u t edit del LF aux hi hθ hb hinner ha hγ hu ht he haux hdel hbad
  have hu':u ≤ 3*θ:=by linarith
  have h:=hbudget n θ b inner a γ u t edit aux del (2*LF)
    (by positivity) hθ hi hb hinner ha hγ hu' ht he haux hdel hbad
  linarith
end Oberwolfach
