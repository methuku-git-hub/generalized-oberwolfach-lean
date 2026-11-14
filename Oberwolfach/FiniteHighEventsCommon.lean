module

public import Oberwolfach.CommonEvents

@[expose] public section
/-! The events may use the same random variables and need not be independent. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_high_events_common {Ω I:Type} [Fintype Ω] (μ:FiniteLaw Ω)
    (T:Finset I) (E:I→Ω→Prop) (ε:I→ℝ)
    (hE:∀ i∈T,1-ε i≤μ.probability (E i)):
    1-∑ i∈T,ε i≤μ.probability (fun ω=>∀ i∈T,E i ω):=by
  have hbad:∀ i∈T,μ.probability (fun ω=>¬E i ω)≤ε i:=by
    intro i hi
    have hh:=finiteLaw_probability_compl μ (E i)
    linarith [hE i hi]
  have hh:=finiteLaw_common_event_lower μ T (fun i ω=>¬E i ω) ε hbad
  simpa only [not_not] using hh
end Oberwolfach
