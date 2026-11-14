module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget

@[expose] public section
/-! A small fixed absorber and a sufficiently small inner set preserve half
of an already selected positive reserved-list rate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_trim_budget_eventually
    (lam ε:ℝ) (B:ℕ) (hlam:0<lam) (hε:ε≤lam/4):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(inner abs:ℕ),
      (inner:ℝ)≤ε*n→abs≤B→(lam/2)*n+inner+abs≤lam*n :=by
  obtain ⟨N,hN⟩:=ordinary_constant_eventually_below_linear_rate (lam/4) B (by positivity)
  refine ⟨N,?_⟩
  intro n hn inner abs hinner habs
  have hbound:(abs:ℝ)≤(B:ℝ):=by exact_mod_cast habs
  have hn0:(0:ℝ)≤n:=by positivity
  have heps:=mul_le_mul_of_nonneg_right hε hn0
  have hconst:=hN n hn
  nlinarith
end Oberwolfach
