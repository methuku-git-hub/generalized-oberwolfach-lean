module

public import Oberwolfach.LongPrescribedMatchingHubMargins
public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_prescribed_matching_hub_asymptotic (b:ℝ) (hb:0<b):
    ∃N:ℕ,∀n≥N,4*(n:ℝ)^(3/4:ℝ)≤b*n/2:=by
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (b/8) 0 (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hh:=hN n hn
  nlinarith only [hh]
end Oberwolfach
