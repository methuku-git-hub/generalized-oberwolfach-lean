module

public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section
/-! A positive hub-density lower bound and sufficiently long intervals make
the protected-pair label budget valid for all large orders. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_protected_pair_budget_before_spacing
    (θ ρ₀:ℝ) (hθ:0<θ) (hρ:0<ρ₀):
    ∃a:ℝ,0<a ∧ ∀(d:ℕ),0<d→1/(4*(d:ℝ))≤5*θ^2/256→∃N:ℕ,∀n:ℕ,N≤n→∀u:ℕ,
      ρ₀*n≤4*(u:ℝ)→
      a*n+5*(n:ℝ)^(3/4:ℝ)≤((5/32:ℝ)*(θ/2)^2-1/(4*(d:ℝ)))*u:=by
  let a:ℝ:=5*ρ₀*θ^2/2048
  have ha:0<a:=by dsimp [a];positivity
  refine ⟨a,ha,?_⟩
  intro d hd hspacing
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (a/5) 0 (by positivity)
  refine ⟨N,?_⟩
  intro n hn u hu
  have hsmall:=hN n hn
  have hu0:(0:ℝ)≤u:=by positivity
  have hcoeff:(5*θ^2/256:ℝ)≤(5/32:ℝ)*(θ/2)^2-1/(4*(d:ℝ)):=by nlinarith
  have hcoeffU:=mul_le_mul_of_nonneg_right hcoeff hu0
  have hscale:=mul_le_mul_of_nonneg_left hu (show (0:ℝ)≤5*θ^2/1024 by positivity)
  dsimp [a] at *
  nlinarith
end Oberwolfach
