module

public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! An event that intersects every event above a failure threshold has at
least the complementary probability. This does not use independence. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_of_large_event_intersection
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (Good:Ω→Prop) (δ:ℝ)
    (h:∀Extra:Ω→Prop,δ<μ.probability Extra→∃ω,Extra ω ∧ Good ω):
    1-δ≤μ.probability Good:=by
  by_contra hn
  have hc:=finiteLaw_probability_compl μ Good
  have hbad:δ<μ.probability (fun ω=>¬Good ω):=by linarith
  obtain ⟨ω,hnot,hgood⟩:=h (fun ω=>¬Good ω) hbad
  exact hnot hgood

theorem finiteLaw_large_event_intersection_with_prior
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (Good Prior:Ω→Prop) (δ ε:ℝ)
    (h:∀Extra:Ω→Prop,δ<μ.probability Extra→∃ω,Extra ω ∧ Good ω)
    (hPrior:1-ε≤μ.probability Prior):
    1-δ-ε≤μ.probability (fun ω=>Good ω ∧ Prior ω):=
  finiteLaw_intersection_lower μ Good Prior δ ε
    (finiteLaw_probability_of_large_event_intersection μ Good δ h) hPrior
end Oberwolfach
