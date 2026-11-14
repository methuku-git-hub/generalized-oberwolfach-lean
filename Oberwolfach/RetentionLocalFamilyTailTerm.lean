module

public import Oberwolfach.RetentionLocalBinomialTail

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem retention_local_family_tail_term
    (A H d:ℕ) (c:ℝ) (hc:0<c) (hA:1≤A)
    (hHup:(H:ℝ)≤A) (hHlo:c*A≤H):
    (H:ℝ)*(1/(A:ℝ)^6)+(A:ℝ)*((d+1:ℕ)*(1/(H:ℝ)^6)) ≤
      (1+((d+1:ℕ):ℝ)/c^6)/(A:ℝ)^3:=by
  have hAp:(0:ℝ)<A:=by exact_mod_cast (show 0<A by omega)
  have hA1:(1:ℝ)≤A:=by exact_mod_cast hA
  have hpow:(c*(A:ℝ))^6≤(H:ℝ)^6:=pow_le_pow_left₀ (le_of_lt (by positivity : 0<c*(A:ℝ))) hHlo 6
  have hA35:(A:ℝ)^3≤(A:ℝ)^5:=pow_le_pow_right₀ hA1 (by omega)
  have hrow:(H:ℝ)/(A:ℝ)^6≤1/(A:ℝ)^3:=by
    calc
      (H:ℝ)/(A:ℝ)^6 ≤ (A:ℝ)/(A:ℝ)^6 := div_le_div_of_nonneg_right hHup (by positivity)
      _ = 1/(A:ℝ)^5 := by field_simp <;> ring
      _ ≤ 1/(A:ℝ)^3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hA35
  have hcol:(A:ℝ)/(H:ℝ)^6≤(1/c^6)/(A:ℝ)^3:=by
    calc
      (A:ℝ)/(H:ℝ)^6 ≤ (A:ℝ)/(c^6*(A:ℝ)^6) := by
        apply div_le_div_of_nonneg_left hAp.le (by positivity)
        simpa only [mul_pow] using hpow
      _ = (1/c^6)/(A:ℝ)^5 := by field_simp <;> ring
      _ ≤ (1/c^6)/(A:ℝ)^3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hA35
  calc
    (H:ℝ)*(1/(A:ℝ)^6)+(A:ℝ)*((d+1:ℕ)*(1/(H:ℝ)^6)) =
        (H:ℝ)/(A:ℝ)^6+((d+1:ℕ):ℝ)*((A:ℝ)/(H:ℝ)^6) := by ring
    _ ≤ 1/(A:ℝ)^3+((d+1:ℕ):ℝ)*((1/c^6)/(A:ℝ)^3) :=
      add_le_add hrow (mul_le_mul_of_nonneg_left hcol (by positivity))
    _ = (1+((d+1:ℕ):ℝ)/c^6)/(A:ℝ)^3 := by ring
end Oberwolfach
