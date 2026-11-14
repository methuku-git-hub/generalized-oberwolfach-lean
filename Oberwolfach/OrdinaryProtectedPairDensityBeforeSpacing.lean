module

public import Oberwolfach.OrdinaryProtectedPairBudgetBeforeSpacing

@[expose] public section
/-! The original factor-density identity supplies the hub lower bound in the
protected-pair assignment budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_protected_pair_budget_density_before_spacing
    (θ ρ₀:ℝ) (hθ:0<θ) (hρ₀:0<ρ₀):
    ∃a:ℝ,0<a ∧ ∀(d:ℕ),0<d→1/(4*(d:ℝ))≤5*θ^2/256→∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] (ρ D:ℝ),
      ρ₀≤ρ→0<D→(n:ℝ)/2≤D→ρ*D=2*(Fintype.card U:ℝ)→
      a*n+5*(n:ℝ)^(3/4:ℝ)≤((5/32:ℝ)*(θ/2)^2-1/(4*(d:ℝ)))*Fintype.card U:=by
  obtain ⟨a,ha,hN⟩:=ordinary_protected_pair_budget_before_spacing θ ρ₀ hθ hρ₀
  refine ⟨a,ha,?_⟩
  intro d hd hspacing
  obtain ⟨N,hN⟩:=hN d hd hspacing
  refine ⟨N,?_⟩
  intro n hn U _ ρ D hρ hD hDlo hsize
  have h₁:=mul_le_mul_of_nonneg_right hρ hD.le
  have h₂:=mul_le_mul_of_nonneg_left hDlo hρ₀.le
  have hU:ρ₀*n≤4*(Fintype.card U:ℝ):=by nlinarith
  exact hN n hn (Fintype.card U) hU
end Oberwolfach
