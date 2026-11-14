module

public import Oberwolfach.FiniteSeedFailureMargins

@[expose] public section
/-! The assigned host event and linear retained-degree error can share any
fixed positive failure budget after the parameters are chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_shared_degree_failure_eventually_small
    (δ χ:ℝ) (hδ:0<δ) (hχ:0<χ):
    ∃N:ℕ,1≤N ∧ ∀n≥N,
      1/(n:ℝ)+3/(n:ℝ)^2+2*(n:ℝ)*Real.exp (-2*(δ*(n:ℝ))^2/n)<χ :=by
  obtain ⟨Nexp,hExp⟩:=eventually_any_polynomial_exponential_failure_below 2 (2*δ^2) (χ/2) 1 (by positivity) (by positivity)
  obtain ⟨Ninv,hInv⟩:=exists_nat_gt (8/χ)
  refine ⟨max 1 (max Nexp Ninv),by omega,?_⟩
  intro n hn
  have hn0:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hn1:(1:ℝ)≤n:=by exact_mod_cast (show 1≤n by omega)
  have hnN:(Ninv:ℝ)≤n:=by exact_mod_cast (show Ninv≤n by omega)
  have hinv:(1:ℝ)/n<χ/8:=by
    have hh:(8/χ:ℝ)<n:=lt_of_lt_of_le hInv hnN
    apply (div_lt_iff₀ hn0).2
    have h:= (div_lt_iff₀ hχ).1 hh
    nlinarith
  have hsq:(1:ℝ)/(n:ℝ)^2≤1/n:=by
    apply one_div_le_one_div_of_le hn0
    nlinarith
  have heq:-2*(δ*(n:ℝ))^2/n=-(2*δ^2)*(n:ℝ):=by field_simp
  have hexp:2*(n:ℝ)*Real.exp (-2*(δ*(n:ℝ))^2/n)<χ/2:=by
    rw [heq]
    simpa only [pow_one] using hExp n (by omega)
  have hpoly:(1:ℝ)/n+3/(n:ℝ)^2<χ/2:=by
    have hthree:3/(n:ℝ)^2≤3*((1:ℝ)/n):=by
      have hh:=mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤3 by norm_num)
      simpa only [div_eq_mul_inv,one_mul] using hh
    linarith only [hthree,hinv]
  linarith only [hpoly,hexp]
end Oberwolfach
