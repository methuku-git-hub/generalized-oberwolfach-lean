module

public import Oberwolfach.FiniteLawLargeEventIntersection

@[expose] public section
/-! Simultaneous high probability for a fixed finite family of good events,
without independence, with an additional prior event on the same sample. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_many_good_events_lower
    {Ω J:Type} [Fintype Ω] (μ:FiniteLaw Ω) (T:Finset J)
    (Good:J→Ω→Prop) (δ:J→ℝ)
    (h:∀j∈T,1-δ j≤μ.probability (Good j)):
    1-∑j∈T,δ j≤μ.probability (fun ω=>∀j∈T,Good j ω):=by
  have hbad:∀j∈T,μ.probability (fun ω=>¬Good j ω)≤δ j:=by
    intro j hj
    have hc:=finiteLaw_probability_compl μ (Good j)
    have hh:=h j hj
    linarith
  have hh:=finiteLaw_common_event_lower μ T (fun j ω=>¬Good j ω) δ hbad
  simpa only [not_not] using hh

theorem finiteLaw_many_good_events_with_prior
    {Ω J:Type} [Fintype Ω] (μ:FiniteLaw Ω) (T:Finset J)
    (Good:J→Ω→Prop) (δ:J→ℝ) (Prior:Ω→Prop) (ε:ℝ)
    (h:∀j∈T,1-δ j≤μ.probability (Good j))
    (hPrior:1-ε≤μ.probability Prior):
    1-(∑j∈T,δ j)-ε≤μ.probability (fun ω=>(∀j∈T,Good j ω) ∧ Prior ω):=
  finiteLaw_intersection_lower μ (fun ω=>∀j∈T,Good j ω) Prior (∑j∈T,δ j) ε
    (finiteLaw_many_good_events_lower μ T Good δ h) hPrior

theorem finiteLaw_many_good_events_with_prior_witness
    {Ω J:Type} [Fintype Ω] (μ:FiniteLaw Ω) (T:Finset J)
    (Good:J→Ω→Prop) (δ:J→ℝ) (Prior:Ω→Prop) (ε:ℝ)
    (h:∀j∈T,1-δ j≤μ.probability (Good j))
    (hPrior:1-ε≤μ.probability Prior)
    (hsmall:(∑j∈T,δ j)+ε<1):
    ∃ω,0<μ.mass ω ∧ (∀j∈T,Good j ω) ∧ Prior ω:=by
  have hh:=finiteLaw_many_good_events_with_prior μ T Good δ Prior ε h hPrior
  have hp:0<μ.probability (fun ω=>(∀j∈T,Good j ω) ∧ Prior ω):=by linarith
  have hn:∀ω∈(Finset.univ:Finset Ω),0≤(if (∀j∈T,Good j ω) ∧ Prior ω then μ.mass ω else 0):=by
    intro ω _
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl
  have heq:μ.probability (fun ω=>(∀j∈T,Good j ω) ∧ Prior ω)=
      ∑ω,(if (∀j∈T,Good j ω) ∧ Prior ω then μ.mass ω else 0):=by
    unfold FiniteLaw.probability
    apply Finset.sum_congr rfl
    intro ω _
    exact (ite_eq_ite ((∀j∈T,Good j ω) ∧ Prior ω) (μ.mass ω) 0).mpr trivial
  rw [heq] at hp
  obtain ⟨ω,_,hω⟩:=(Finset.sum_pos_iff_of_nonneg hn).mp hp
  split_ifs at hω with hg
  · exact ⟨ω,hω,hg⟩
  · exact (lt_irrefl _ hω).elim
end Oberwolfach
