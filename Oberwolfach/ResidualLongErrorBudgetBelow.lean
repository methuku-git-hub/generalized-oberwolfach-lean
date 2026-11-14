module

public import Oberwolfach.ResidualLongErrorBudget

@[expose] public section
/-! Retention error may be reduced below any specified positive margin. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem residual_long_error_budget_below
    (m d:ℕ) (hm:0<m) (hd:1≤d) (θ ζMax:ℝ) (hθ:0<θ) (hMax:0<ζMax)
    (hcut:1/(((m:ℝ)+1)*(d:ℝ))≤θ):
    ∃ζ:ℝ,0<ζ ∧ ζ≤ζMax ∧ ∃N:ℕ,∀n:ℕ,N≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤4*θ*n:=by
  obtain ⟨ζ₀,hζ₀,N,hN⟩:=residual_long_error_budget m d hm hd θ hθ hcut
  let ζ:=min ζ₀ ζMax
  have hζ:0<ζ:=lt_min hζ₀ hMax
  have hle:ζ≤ζ₀:=min_le_left _ _
  refine ⟨ζ,hζ,min_le_right _ _,N,?_⟩
  intro n hn q err hq herr
  have hcoeff:0≤(((m+1)*d-1:ℕ):ℝ):=Nat.cast_nonneg _
  have hh:=mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg n)
  have hh':=mul_le_mul_of_nonneg_left hh hcoeff
  have h:=hN n hn q err hq herr
  nlinarith
end Oberwolfach
