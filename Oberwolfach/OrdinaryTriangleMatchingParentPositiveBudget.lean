module

public import Oberwolfach.OrdinaryTriangleParentSamplePositiveBudget

@[expose] public section
/-! Choose the matching failure first, then reserve a uniform positive budget
for all triangle and parent events on the common sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_matching_parent_positive_budget
    (baseLoss ζcap:ℝ) (hbase:baseLoss<1) (hζcap:0<ζcap):
    ∃ζMatch:ℝ,0<ζMatch ∧ ζMatch≤ζcap ∧ baseLoss+ζMatch<1 ∧
    ∃χcap:ℝ,0<χcap ∧ ∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀χtwo χrows χdeep χcut χHub χEndpoint χhost χref:ℝ,
    χtwo≤χcap→χrows≤χcap→χdeep≤χcap→χcut≤χcap→χHub≤χcap→χEndpoint≤χcap→χhost≤χcap→χref≤χcap→
    0<1-(((((((baseLoss+ζMatch)+χtwo)+χrows)+χdeep)+χcut)+χHub)+χEndpoint)-
      2/(n:ℝ)^10-(1/(n:ℝ)+2/(n:ℝ)^2)-χhost-χref :=by
  let ζMatch:ℝ:=min ζcap (1-baseLoss)/4
  have hζ:0<ζMatch:=by dsimp [ζMatch];positivity
  have hζcap':ζMatch≤ζcap:=by
    have hh:=min_le_left ζcap (1-baseLoss)
    dsimp [ζMatch]
    linarith
  have hmargin:baseLoss+ζMatch<1:=by
    have hh:=min_le_right ζcap (1-baseLoss)
    dsimp [ζMatch]
    linarith
  obtain ⟨χcap,hχcap,N,hN,hbudget⟩:=ordinary_triangle_parent_sample_positive_budget (baseLoss+ζMatch) hmargin
  exact ⟨ζMatch,hζ,hζcap',hmargin,χcap,hχcap,N,hN,hbudget⟩
end Oberwolfach
