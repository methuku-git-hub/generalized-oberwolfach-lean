module

public import Oberwolfach.OrdinaryCombinedSamplePositiveBudget

@[expose] public section
/-! The triangle reservoir, matching prior, two-step tests, parent event
and reference cuts fit inside a positive common probability margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_sample_positive_budget
    (lossE:ℝ) (hmargin:lossE<1):
    ∃χcap:ℝ,0<χcap ∧ ∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀χtwo χrows χdeep χcut χHub χEndpoint χhost χref:ℝ,
    χtwo≤χcap→χrows≤χcap→χdeep≤χcap→χcut≤χcap→χHub≤χcap→χEndpoint≤χcap→χhost≤χcap→χref≤χcap→
    0<1-((((((lossE+χtwo)+χrows)+χdeep)+χcut)+χHub)+χEndpoint)-
      2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2)-χhost-χref :=by
  obtain ⟨χlarge,hχlarge,N,hN,hbudget⟩:=ordinary_combined_sample_positive_budget lossE hmargin
  let χcap:ℝ:=χlarge/2
  have hχcap:0<χcap:=by dsimp [χcap];linarith
  have hcap:χcap≤χlarge:=by dsimp [χcap];linarith
  refine ⟨χcap,hχcap,N,hN,?_⟩
  intro n hn χtwo χrows χdeep χcut χHub χEndpoint χhost χref htwo hrows hdeep hcut hHub hEndpoint hhost href
  have hsum:χhost+χref≤χlarge:=by dsimp [χcap] at hhost href;linarith
  have hh:=hbudget n hn χtwo χrows χdeep χcut χHub χEndpoint (χhost+χref)
    (htwo.trans hcap) (hrows.trans hcap) (hdeep.trans hcap) (hcut.trans hcap) (hHub.trans hcap) (hEndpoint.trans hcap) hsum
  linarith only [hh]
end Oberwolfach
