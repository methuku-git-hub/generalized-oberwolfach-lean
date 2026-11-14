module

public import Mathlib.Tactic

@[expose] public section
/-! A fixed-domain triangle event with loss 1/W + 3/W² has loss at most
4/A when its domain contains a set of size A at least one. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_failure_arithmetic (A W:ℝ) (hA:0<A) (hAW:A≤W) (hWone:1≤W):
    1-1/(A/4)≤1-(1/W+3/W^2) :=by
  have hW:0<W:=hA.trans_le hAW
  have hinv:1/W≤1/A:=one_div_le_one_div_of_le hA hAW
  have hsq:1/W^2≤1/W:=by
    apply (div_le_div_iff₀ (sq_pos_of_pos hW) hW).2
    nlinarith only [hWone,hW]
  have hid:1/(A/4)=4/A:=by ring
  rw [hid]
  simp only [div_eq_mul_inv,one_mul] at hinv hsq ⊢
  linarith only [hinv,hsq]
end Oberwolfach
