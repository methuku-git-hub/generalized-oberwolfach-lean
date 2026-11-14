module

public import Oberwolfach.OrdinarySharedDegreeFailureBudget

@[expose] public section
/-! The prescribed-wheel event adds only one inverse-order term to the
ordinary host and degree failure budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_prescribed_failure_eventually_small
    (δ χ:ℝ) (hδ:0<δ) (hχ:0<χ):
    ∃N:ℕ,1≤N ∧ ∀n≥N,
      (1/(n:ℝ)+3/(n:ℝ)^2+2*(n:ℝ)*Real.exp (-2*(δ*(n:ℝ))^2/n))+1/(n:ℝ)<χ :=by
  obtain ⟨N,hN,hbase⟩:=ordinary_shared_degree_failure_eventually_small δ (χ/2) hδ (by positivity)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hnpos:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hnonneg:0≤3/(n:ℝ)^2+2*(n:ℝ)*Real.exp (-2*(δ*(n:ℝ))^2/n):=by positivity
  have hh:=hbase n hn
  linarith
end Oberwolfach
