module

public import Oberwolfach.OrdinarySharedDegreeFailureBudget

@[expose] public section
/-! The correction-coin and constructed-reservoir failure terms fit any
fixed positive budget by choosing the graph order sufficiently large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_correction_failure_eventually_small
    (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,1≤N ∧ ∀n≥N,
      2/(n:ℝ)^1+(1/(n:ℝ)+2/(n:ℝ)^2)<χ :=by
  obtain ⟨N,hN,hbase⟩:=ordinary_shared_degree_failure_eventually_small 1 (χ/6) (by norm_num) (by positivity)
  refine ⟨N,hN,?_⟩
  intro n hn
  have hn0:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hn1:(1:ℝ)≤n:=by exact_mod_cast (show 1≤n by omega)
  have hsq:(1:ℝ)/(n:ℝ)^2≤1/n:=by
    apply one_div_le_one_div_of_le hn0
    nlinarith
  have hnonneg:0≤3/(n:ℝ)^2+2*(n:ℝ)*Real.exp (-2*((1:ℝ)*n)^2/n):=by positivity
  have hh:=hbase n hn
  have htwo:2/(n:ℝ)^2≤2*((1:ℝ)/n):=by
    have h:=mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤2 by norm_num)
    simpa only [div_eq_mul_inv,one_mul] using h
  simp only [pow_one,div_eq_mul_inv,one_mul] at hnonneg hh htwo ⊢
  linarith
end Oberwolfach
