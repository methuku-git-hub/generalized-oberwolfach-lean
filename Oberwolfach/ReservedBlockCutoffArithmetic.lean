module

public import Oberwolfach.ReservedCapacitySufficient

@[expose] public section
/-! The reserved-block surplus calculation with the manuscript's cutoff and
error bounds, separated from the counting and power estimates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reserved_block_surplus_of_cutoff
    (n ell t K theta err : ℝ)
    (hn : 0 ≤ n) (ht : 0 < t) (hK : 0 < K) (hθ : 0 < theta)
    (hell : (1:ℝ)/2 ≤ ell)
    (hcut : 5/(t+5) + t/K ≤ theta/2)
    (herr : err < theta*n/(4*t)) :
    (1-theta)*ell*n/t + err < ell*n/(t+5) - ell*n/K := by
  have hgap : theta/2 ≤ theta - 5/(t+5) - t/K := by linarith
  have hbase : n/(2*t) ≤ ell*n/t := by
    have hmul : n/2 ≤ ell*n := by nlinarith
    have hd := div_le_div_of_nonneg_right hmul (le_of_lt ht)
    convert hd using 1 <;> ring
  have hprod : theta*n/(4*t) ≤ (ell*n/t)*(theta - 5/(t+5) - t/K) := by
    calc
      theta*n/(4*t) = (n/(2*t))*(theta/2) := by ring
      _ ≤ (ell*n/t)*(theta/2) := mul_le_mul_of_nonneg_right hbase (by positivity)
      _ ≤ (ell*n/t)*(theta - 5/(t+5) - t/K) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
  have hid : ell*n/(t+5) - ell*n/K - (1-theta)*ell*n/t =
      (ell*n/t)*(theta - 5/(t+5) - t/K) := by
    field_simp
    <;> ring
  linarith
end Oberwolfach
