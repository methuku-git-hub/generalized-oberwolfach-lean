module

public import Oberwolfach.OrdinaryCombinedSamplePositiveBudget

@[expose] public section
/-! Allocate failure probabilities for the triangle reservoir, two-step
balance, endpoint and cover events within the prior's positive margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_combined_sample_positive_budget
    (lossE:ℝ) (hmargin:lossE<1):
    ∃χcap:ℝ,0<χcap ∧ ∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀χtwo χrows χdeep χcut χHub χEndpoint:ℝ,
    χtwo≤χcap→χrows≤χcap→χdeep≤χcap→χcut≤χcap→χHub≤χcap→χEndpoint≤χcap→
    0<1-((((((lossE+χtwo)+χrows)+χdeep)+χcut)+χHub)+χEndpoint)-
      2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2) :=by
  obtain ⟨χcap,hχ,N,hN,hbudget⟩:=ordinary_combined_sample_positive_budget lossE hmargin
  refine ⟨χcap,hχ,N,hN,?_⟩
  intro n hn χtwo χrows χdeep χcut χHub χEndpoint htwo hrows hdeep hcut hHub hEndpoint
  have hh:=hbudget n hn χtwo χrows χdeep χcut χHub χEndpoint 0 htwo hrows hdeep hcut hHub hEndpoint hχ.le
  linarith only [hh]
end Oberwolfach
