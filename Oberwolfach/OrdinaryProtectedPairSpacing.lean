module

public import Oberwolfach.OrdinaryProtectedPairBudgetDensity

@[expose] public section
/-! The interval-length parameter can be chosen to meet the protected-pair
loss bound before the ambient order is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_protected_pair_spacing_choice (θ:ℝ) (hθ:0<θ):
    ∃D:ℕ,∀d:ℕ,D≤d→0<d ∧ 1/(4*(d:ℝ))≤5*θ^2/256:=by
  have hs:0<5*θ^2:=by positivity
  obtain ⟨D,hD⟩:=exists_nat_gt (64/(5*θ^2))
  refine ⟨max D 1,?_⟩
  intro d hd
  have hd0:0<d:=by omega
  have hdR:0<(d:ℝ):=by exact_mod_cast hd0
  have hh:64/(5*θ^2)≤(d:ℝ):=le_of_lt (lt_of_lt_of_le hD (by exact_mod_cast (show D≤d by omega)))
  have hh':64≤(d:ℝ)*(5*θ^2):=(div_le_iff₀ hs).1 hh
  refine ⟨hd0,?_⟩
  apply (div_le_iff₀ (show 0<4*(d:ℝ) by positivity)).2
  nlinarith
end Oberwolfach
