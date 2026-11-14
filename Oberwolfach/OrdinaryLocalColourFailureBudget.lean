module

public import Oberwolfach.FiniteSeedFailureMargins

@[expose] public section
/-! A fixed local relative error has an arbitrarily small failure probability
once the inner set is sufficiently large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_local_colour_failure_budget
    (ζ χ:ℝ) (hζ:0<ζ) (hχ:0<χ):
    ∃N:ℕ,1≤N ∧ ∀n≥N,
      12*(n:ℝ)*Real.exp (-2*(ζ*(n:ℝ))^2/n)<χ :=by
  obtain ⟨Nexp,hExp⟩:=eventually_any_polynomial_exponential_failure_below 12 (2*ζ^2) χ 1 (by positivity) hχ
  refine ⟨max 1 Nexp,by omega,?_⟩
  intro n hn
  have hn0:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have heq:-2*(ζ*(n:ℝ))^2/n=-(2*ζ^2)*(n:ℝ):=by field_simp
  rw [heq]
  simpa only [pow_one] using hExp n (by omega)
end Oberwolfach
