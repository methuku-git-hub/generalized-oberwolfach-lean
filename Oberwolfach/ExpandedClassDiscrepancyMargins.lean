module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The six-state degree error is sublinear. The original host error and the
regularisation edit rate can be chosen before the order threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem eventually_expanded_class_discrepancy (c:ℝ) (hc:0<c):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ρ ε ξ:ℝ,
      0≤ρ→ρ≤1→0≤ε→ε≤c/2→ξ≤c/4→
      5*(n:ℝ)^(3/5:ℝ)+ρ/2*(ε*n)+ξ*n≤c*n:=by
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 5 0 1 (2/5) (c/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  refine ⟨N,?_⟩
  intro n hn ρ ε ξ hρ hρhi hε hεhi hξ
  have hsmall:=hN n hn ((n:ℝ)^(3/5:ℝ)) (by norm_num)
  have hrho:ρ*ε≤ε:=by nlinarith [mul_nonneg (sub_nonneg.mpr hρhi) hε]
  have hcε:ρ/2*ε≤c/4:=by linarith
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hE:=mul_le_mul_of_nonneg_right hcε hn0
  have hX:=mul_le_mul_of_nonneg_right hξ hn0
  nlinarith
end Oberwolfach
