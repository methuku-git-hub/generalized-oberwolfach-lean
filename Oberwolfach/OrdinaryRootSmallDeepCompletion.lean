module

public import Oberwolfach.OrdinaryGeneralFinishAfterDensity

@[expose] public section
/-! The stronger deep-set bound already used for root-first cleanup also
    pays the general-wheel completion's forbidden-vertex allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_root_small_deep_completion (p βe n size:ℝ)
    (hp:0≤p) (hp1:p≤1) (hβ:0≤βe) (hn:0≤n)
    (hsize:size≤((p^3*βe/2)/2)*n):
    size≤(βe/2)*n :=by
  have hp3:p^3≤1:=pow_le_one₀ hp hp1
  have hmul:=mul_le_mul_of_nonneg_right hp3 (mul_nonneg hβ hn)
  nlinarith only [hsize,hmul,mul_nonneg hβ hn]
end Oberwolfach
