module

public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! An exponential number of cut tests with a quadratic exponential tail
still has a uniform linear exponential failure bound. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem eventually_allCuts_failure_exponential {c : ℝ} (hc : 0<c) :
    ∃ N : ℕ,1≤N ∧ ∀ n : ℕ,N≤n → ∀ C : ℝ,0≤C →
      C*(4:ℝ)^n*Real.exp (-c*(n:ℝ)^2)≤C*Real.exp (-(c/2)*n) := by
  let N := max 1 (Nat.ceil (2*Real.log 4/c))
  refine ⟨N,le_max_left _ _,?_⟩
  intro n hn C hC
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by dsimp [N] at hn;omega)
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hceil : (Nat.ceil (2*Real.log 4/c):ℝ)≤n := by
    exact_mod_cast (show Nat.ceil (2*Real.log 4/c)≤n by dsimp [N] at hn;omega)
  have hh : 2*Real.log 4/c≤(n:ℝ) := (Nat.le_ceil _).trans hceil
  have hlog := (div_le_iff₀ hc).mp hh
  have hmul := mul_le_mul_of_nonneg_right hlog hn0
  have hexp : (n:ℝ)*Real.log 4-c*(n:ℝ)^2≤-(c/2)*(n:ℝ)^2 := by nlinarith only [hmul]
  have heq : (4:ℝ)^n=Real.exp ((n:ℝ)*Real.log 4) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]
  calc
    _ = C*Real.exp ((n:ℝ)*Real.log 4-c*(n:ℝ)^2) := by rw [heq,Real.exp_sub];rw [div_eq_mul_inv,← Real.exp_neg];ring
    _ ≤ C*Real.exp (-(c/2)*(n:ℝ)^2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.exp_le_exp.mpr
      have hn2 : (n:ℝ)≤(n:ℝ)^2 := by nlinarith only [hn1]
      exact mul_le_mul_of_nonpos_left hn2 (by linarith)

end Oberwolfach
