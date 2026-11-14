module

public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section
/-! The manuscript's fixed reserved-list coefficient leaves room for both
sublinear concentration and the fixed separation loss at large host order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_list_concentration_margins
    (αHost ρ₀:ℝ) (hα:0<αHost) (hρ:0<ρ₀) (d:ℕ):
    ∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      ((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)*n+(n:ℝ)^(3/4:ℝ)≤
        αHost*(ρ₀/200)^2*n*(1/100:ℝ) := by
  let a:ℝ:=αHost*(ρ₀/200)^2
  have ha:0<a:=by dsimp [a];positivity
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (a/10000)
    (2*(2*((3*d:ℕ):ℝ)+1)) (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hn0:(0:ℝ)≤n:=by positivity
  have hconst:0≤2*(2*((3*d:ℕ):ℝ)+1):=by positivity
  have hmin:=mul_le_mul_of_nonneg_right (min_le_left αHost (1/4:ℝ)) (sq_nonneg (ρ₀/200))
  have hβ:((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)≤a/1600:=by
    dsimp [a]
    nlinarith only [hmin]
  have hβn:=mul_le_mul_of_nonneg_right hβ hn0
  have h:=hN n hn
  constructor
  · have hacap:a/10000≤a:=by linarith
    exact h.trans (by simpa only [a] using mul_le_mul_of_nonneg_right hacap hn0)
  · have han:0≤a*(n:ℝ):=mul_nonneg ha.le hn0
    have herr:(n:ℝ)^(3/4:ℝ)≤a/10000*n:=by linarith
    have hc:(1/1600:ℝ)+(1/10000)≤1/100:=by norm_num
    have hh:=mul_le_mul_of_nonneg_right hc han
    change ((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)*n+(n:ℝ)^(3/4:ℝ)≤a*n*(1/100:ℝ)
    nlinarith only [hβn,herr,hh]
end Oberwolfach
