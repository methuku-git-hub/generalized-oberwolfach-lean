module

public import Mathlib.Tactic

@[expose] public section
/-! The fixed long-sample hub density makes the parent-load denominator
identical to the denominator in the uniform level theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reference_parent_load_scale_alignment
    (m:ℕ) (ρ₀ sstar tstar:ℝ) (ht:tstar=sstar/(m:ℝ)):
    ρ₀*tstar/2=ρ₀*sstar/(2*(m:ℝ)) := by
  rw [ht]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
end Oberwolfach
