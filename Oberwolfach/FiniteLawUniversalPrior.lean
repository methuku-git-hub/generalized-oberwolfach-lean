module

public import Oberwolfach.CommonEvents

@[expose] public section
/-! A uniform intersection principle gives a lower bound for its projected
witness event, without requiring independence. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_of_universal_prior_witness
    {Ω:Type*} [Fintype Ω] (μ:FiniteLaw Ω) (Good:Ω→Prop) (ε:ℝ)
    (h:∀ Prior:Ω→Prop,1-ε≤μ.probability Prior→∃ω,Prior ω ∧ Good ω):
    ε<μ.probability Good :=by
  by_contra hn
  have hc:=finiteLaw_probability_compl μ Good
  have hp:1-ε≤μ.probability (fun ω=>¬Good ω):=by linarith
  obtain ⟨ω,hbad,hgood⟩:=h (fun ω=>¬Good ω) hp
  exact hbad hgood
theorem finiteLaw_join_projected_witness_with_endpoint
    {Ω Ξ:Type*} [Fintype Ω] (μ:FiniteLaw Ω) (project:Ξ→Ω)
    (Good:Ξ→Prop) (Endpoint:Ω→Prop) (ε:ℝ)
    (hmatch:∀ Prior:Ω→Prop,1-ε≤μ.probability Prior→∃x:Ξ,Prior (project x) ∧ Good x)
    (hendpoint:∀ Extra:Ω→Prop,ε≤μ.probability Extra→∃y:Ω,Extra y ∧ Endpoint y):
    ∃x:Ξ,Good x ∧ Endpoint (project x) :=by
  let ProjectedGood:=fun y:Ω=>∃x:Ξ,project x=y ∧ Good x
  have hProb:ε<μ.probability ProjectedGood:=by
    apply finiteLaw_probability_of_universal_prior_witness μ ProjectedGood ε
    intro Prior hPrior
    obtain ⟨x,hx,hgood⟩:=hmatch Prior hPrior
    exact ⟨project x,hx,x,rfl,hgood⟩
  obtain ⟨y,⟨x,hxy,hgood⟩,hend⟩:=hendpoint ProjectedGood hProb.le
  exact ⟨x,hgood,hxy.symm ▸ hend⟩
end Oberwolfach
