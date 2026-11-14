module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! The protected-partition failure bound is at most one half once the
host has at least two vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem partition_failure_at_most_half (n:ℕ) (hn:2≤n):
    (1:ℝ)/(n:ℝ)^10≤1/2:=by
  have hnR:(2:ℝ)≤n:=by exact_mod_cast hn
  have hn0:(0:ℝ)≤n:=by linarith
  have hpow:(1:ℝ)≤(n:ℝ)^9:=one_le_pow₀ (by linarith)
  have hh:0≤(n:ℝ)*((n:ℝ)^9-1):=mul_nonneg hn0 (by linarith)
  have hn10:(2:ℝ)≤(n:ℝ)^10:=by nlinarith [show (n:ℝ)^10=(n:ℝ)*(n:ℝ)^9 by ring]
  exact one_div_le_one_div_of_le (by norm_num) hn10
end Oberwolfach
