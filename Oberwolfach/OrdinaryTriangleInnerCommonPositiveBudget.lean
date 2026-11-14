module

public import Oberwolfach.OrdinaryTriangleParentSamplePositiveBudget

@[expose] public section
/-! The matching, correction, parent and reference common event remains
positive after adding the fine cover and the inner hub-weight event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_common_positive_budget
    (lossE:ℝ) (hmargin:lossE<1):
    ∃χcap:ℝ,0<χcap ∧ ∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀χtwo χrows χdeep χcut χHub χEndpoint χhost χref χinner χfine:ℝ,
    χtwo≤χcap→χrows≤χcap→χdeep≤χcap→χcut≤χcap→χHub≤χcap→χEndpoint≤χcap→
    χhost≤χcap→χref≤χcap→χinner≤χcap→χfine≤χcap→
    0<1-((((((lossE+χtwo)+χrows)+χdeep)+χcut)+χHub)+χEndpoint)-
      2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2)-χhost-χref-χinner-χfine:=by
  obtain ⟨χlarge,hχlarge,N,hN,hbudget⟩:=ordinary_triangle_parent_sample_positive_budget lossE hmargin
  let χcap:ℝ:=χlarge/3
  have hχcap:0<χcap:=by dsimp [χcap];linarith
  have hcap:χcap≤χlarge:=by dsimp [χcap];linarith
  refine ⟨χcap,hχcap,N,hN,?_⟩
  intro n hn χtwo χrows χdeep χcut χHub χEndpoint χhost χref χinner χfine
    htwo hrows hdeep hcut hHub hEndpoint hhost href hinner hfine
  have hsum:χhost+χinner+χfine≤χlarge:=by dsimp [χcap] at hhost hinner hfine;linarith
  have hh:=hbudget n hn χtwo χrows χdeep χcut χHub χEndpoint (χhost+χinner+χfine) χref
    (htwo.trans hcap) (hrows.trans hcap) (hdeep.trans hcap) (hcut.trans hcap)
    (hHub.trans hcap) (hEndpoint.trans hcap) hsum (href.trans hcap)
  linarith only [hh]
end Oberwolfach
