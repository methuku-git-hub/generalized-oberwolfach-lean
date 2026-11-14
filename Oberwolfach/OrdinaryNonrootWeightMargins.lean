module

public import Oberwolfach.OrdinaryNonrootCountMargins

@[expose] public section
/-! Explicit scale choices and error bounds for weights restricted to a
large nonroot vertex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_weight_scales (n m κ b B:ℝ) (p:ℕ)
    (hn:0<n) (hκ:0<κ) (hmn:m≤n) (hκn:κ*n≤m) (hb:0≤b) (hB:0≤B):
    b*κ^p/m^p≤b/n^p ∧ B/n^p≤B/m^p:=by
  have hm:0<m:=lt_of_lt_of_le (mul_pos hκ hn) hκn
  have hp:(κ*n)^p≤m^p:=pow_le_pow_left₀ (mul_nonneg hκ.le hn.le) hκn p
  rw [mul_pow] at hp
  constructor
  · apply (div_le_div_iff₀ (pow_pos hm p) (pow_pos hn p)).mpr
    have hh:=mul_le_mul_of_nonneg_left hp hb
    nlinarith only [hh]
  · exact div_le_div_of_nonneg_left hB (pow_pos hm p) (pow_le_pow_left₀ hm.le hmn p)

theorem ordinary_nonroot_weight_error_margin (n t lam R B:ℝ)
    (hn:0<n) (hR:0≤R) (hB:0≤B) (hsize:t≤lam*n):
    t*(R*B/n)≤lam*R*B:=by
  have hh:=mul_le_mul_of_nonneg_right hsize (div_nonneg (mul_nonneg hR hB) hn.le)
  calc
    _ ≤ (lam*n)*(R*B/n):=hh
    _ = lam*R*B:=by field_simp <;> ring
end Oberwolfach
