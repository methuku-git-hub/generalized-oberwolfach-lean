module

public import Oberwolfach.FiniteInverseSquareBound

@[expose] public section
/-! A uniform tail bound for distinct positive integer sizes. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem inverse_cube_finset_tail_bound (T:Finset ℕ) (m:ℕ) (hm:1≤m)
    (hT:∀k∈T,m≤k) : (∑ k∈T, (1:ℝ)/(k:ℝ)^3) ≤ 8/(m:ℝ) := by
  have hmR:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have hterm : ∀k∈T,(1:ℝ)/(k:ℝ)^3 ≤ (4/(m:ℝ))*((1:ℝ)/((k:ℝ)+1)^2) := by
    intro k hk
    have hmk:(m:ℝ)≤k:=by exact_mod_cast hT k hk
    have hkR:(1:ℝ)≤k:=le_trans (by exact_mod_cast hm) hmk
    have hkpos:(0:ℝ)<k:=by linarith
    have hquad:((k:ℝ)+1)^2≤4*(k:ℝ)^2:=by nlinarith
    have hprod : (m:ℝ)*((k:ℝ)+1)^2≤4*(k:ℝ)^3 := by
      calc
        _ ≤ (k:ℝ)*((k:ℝ)+1)^2 := mul_le_mul_of_nonneg_right hmk (sq_nonneg _)
        _ ≤ (k:ℝ)*(4*(k:ℝ)^2) := mul_le_mul_of_nonneg_left hquad hkpos.le
        _ = _ := by ring
    have hident:(4/(m:ℝ))*((1:ℝ)/((k:ℝ)+1)^2)=4/((m:ℝ)*((k:ℝ)+1)^2) := by
      field_simp
    rw [hident]
    apply (div_le_div_iff₀ (pow_pos hkpos 3) (mul_pos hmR (sq_pos_of_pos (by linarith)))).2
    simpa using hprod
  calc
    _ ≤ ∑k∈T,(4/(m:ℝ))*((1:ℝ)/((k:ℝ)+1)^2) := Finset.sum_le_sum hterm
    _ = (4/(m:ℝ))*(∑k∈T,(1:ℝ)/((k:ℝ)+1)^2) := by rw [Finset.mul_sum]
    _ ≤ (4/(m:ℝ))*2 := mul_le_mul_of_nonneg_left (inverse_square_finset_bound T) (by positivity)
    _ = _ := by ring
end Oberwolfach
