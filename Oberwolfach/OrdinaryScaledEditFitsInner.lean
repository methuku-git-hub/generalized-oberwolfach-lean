module

public import Oberwolfach.OrdinaryDeepCommonRatesBeforeFailure

@[expose] public section
/-! A global target edit and the correction fit the smaller first-vortex
scale when both rates were chosen proportionally to the contraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_scaled_edit_fits_inner
    (cap ε ξedit ξAbs N Z:ℝ) (hcap:0≤cap) (hε:0≤ε) (hN:0≤N)
    (hZ:ε*N/2≤Z) (hEdit:ξedit≤cap*ε/1000) (hAbs:ξAbs≤cap*ε/1000):
    ξedit*N+10*ξAbs*N≤cap*Z/4 :=by
  have hE:=mul_le_mul_of_nonneg_right hEdit hN
  have hA:=mul_le_mul_of_nonneg_right hAbs hN
  have hZ':=mul_le_mul_of_nonneg_left hZ hcap
  have hnonneg:0≤cap*ε*N:=mul_nonneg (mul_nonneg hcap hε) hN
  nlinarith only [hE,hA,hZ',hnonneg]
end Oberwolfach
