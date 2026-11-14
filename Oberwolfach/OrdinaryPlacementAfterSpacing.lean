module

public import Oberwolfach.OrdinaryPlacementMatchingRateBounds

@[expose] public section
/-! Numerical placement estimates once the common spacing is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryPlacementAfterSpacing
    (m d N:ℕ) (α δ θ κ b z matchErr ζret:ℝ):Prop :=
      0<ζret ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z ≤ θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ ≤ δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+matchErr ≤ (δ/8)/2 ∧
      1 ≤ N ∧ (∀n:ℕ,N ≤ n → 4/(d:ℝ) ≤ δ/16 ∧ 4*(n:ℝ)^(3/4:ℝ) ≤ δ*n/16)
end Oberwolfach
