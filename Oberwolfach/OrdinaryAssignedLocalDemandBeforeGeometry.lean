module

public import Oberwolfach.OrdinaryLocalDemandBudgetBeforeRates
public import Oberwolfach.OrdinaryActualLocalPostmatchingDemand

@[expose] public section
/-! The original assigned law's local exceptional coefficient is at most
twice θ. A contraction chosen before θ then fits the post-matching demand
inside the later placement budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_local_demand_before_geometry
    (α cap:ℝ) (hα:0<α) (hcap:0<cap):
    ∃ε:ℝ,0<ε ∧ ε≤cap ∧ ∀(n:ℕ) (Inner:Finset (Fin n))
      (θ b a γ u t edit del LF:ℝ) (d:ℕ) (G:SimpleGraph (Fin n)),
      0≤θ → min (α/4096) (1/2:ℝ)*θ≤b →
      (Inner.card:ℝ)≤ε*n → a≤b/16 → γ≤θ → u≤2*θ → t≤θ*Inner.card →
      edit≤b*n/16 → ((6*d+4:ℕ):ℝ)≤b*n/16 → del≤b*n/16 → 2*LF≤b*n/16 →
      (∀v,(G.degree v:ℝ)≤edit+(max (a*n) (γ*Inner.card)+u*Inner.card+3*t+
        (6*d+4:ℕ)+del+LF)+LF) →
      ∀v,(G.degree v:ℝ)≤b*n :=by
  let c:ℝ:=min (α/4096) (1/2:ℝ)
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨ε,hε,hεcap,hbudget⟩:=ordinary_local_demand_budget_before_rates c cap hc hcap
  refine ⟨ε,hε,hεcap,?_⟩
  intro n Inner θ b a γ u t edit del LF d G hθ hb hinner ha hγ hu ht he haux hdel hbad hG v
  have hu':u≤3*θ:=by linarith
  have h:=hbudget n θ b Inner.card a γ u t edit ((6*d+4:ℕ):ℝ) del (2*LF)
    (by positivity) hθ (by positivity) hb hinner ha hγ hu' ht he haux hdel hbad
  have hv:=hG v
  linarith
end Oberwolfach
