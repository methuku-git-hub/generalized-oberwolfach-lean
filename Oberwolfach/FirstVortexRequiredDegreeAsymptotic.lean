module

public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_required_degree_errors_eventually
    (ε δ:ℝ) (d:ℕ) (hε:0<ε) (hδ:0<δ):
    ∃N:ℕ,∀n≥N,∀A:ℕ,ε*n/2≤A→
      (n:ℝ)^(3/4:ℝ)+(6*d+2:ℕ)≤δ*A/16:=by
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (δ*ε/32) ((6*d+2:ℕ):ℝ) (by positivity)
  refine ⟨N,?_⟩
  intro n hn A hA
  have hh:=hN n hn
  have hA':=mul_le_mul_of_nonneg_left hA hδ.le
  nlinarith only [hh,hA']
end Oberwolfach
