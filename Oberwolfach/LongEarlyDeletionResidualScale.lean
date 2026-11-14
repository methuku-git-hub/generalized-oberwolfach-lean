module

public import Oberwolfach.LongEarlyMatchingUniformResidualInput

@[expose] public section

/-! A capped early deletion fits the residual embedding scale, which also
absorbs the later concentration error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_early_deletion_residual_scale
    (eps ζEarly ξLater:ℝ) (heps:0<eps) (hζ:0≤ζEarly)
    (hζcap:ζEarly≤eps/8) (hξ:0≤ξLater) (hξcap:4*ξLater≤eps/2):
    ∃ξResidual:ℝ,0≤ξResidual ∧ 4*ξResidual≤eps/2 ∧
      ζEarly≤ξResidual ∧ ξLater≤ξResidual ∧
      ∀n:ℕ,(ζEarly:ℝ)*n≤ξResidual*n ∧ ξLater*n≤ξResidual*n := by
  refine ⟨eps/8,by positivity,by linarith,hζcap,by linarith,?_⟩
  intro n
  exact ⟨mul_le_mul_of_nonneg_right hζcap (Nat.cast_nonneg n),
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)⟩
end Oberwolfach
