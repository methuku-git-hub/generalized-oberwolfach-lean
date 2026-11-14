module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Numerical bounds on the marked and ordinary hub marginals from the
long-component fraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_marginal_bounds
    (c θ ℓ f:ℝ) (hc:4≤c) (hθ0:0≤θ) (hθ:θ≤1/100)
    (hℓ:1/2≤ℓ) (hℓ1:ℓ≤1) (hf:0≤f):
    let t:=(1/100:ℝ)/(c-1)
    let a:=(1-θ)*ℓ/c-t
    let b:=(c-1)*a+(1-θ)*f;
    1/(3*c)≤a ∧ 1/4≤b ∧ t+a≤1/c:=by
  intro t a b
  have hc0:0<c:=by linarith
  have hcm:0<c-1:=by linarith
  have hθ1:0≤1-θ:=by linarith
  have hprod:(99/100:ℝ)*(1/2)≤(1-θ)*ℓ:=by
    apply mul_le_mul (by linarith : (99/100:ℝ)≤1-θ) hℓ (by norm_num) (by linarith)
  have ht:t≤1/(50*c):=by
    dsimp [t]
    apply (div_le_div_iff₀ hcm (by positivity:0<50*c)).2
    nlinarith
  have ha:1/(3*c)≤a:=by
    dsimp [a]
    have hh:((99/100:ℝ)*(1/2))/c≤((1-θ)*ℓ)/c:=div_le_div_of_nonneg_right hprod hc0.le
    have hnum:(1/(3*c):ℝ)+1/(50*c)≤((99/100:ℝ)*(1/2))/c:=by
      field_simp
      <;> norm_num
    linarith
  refine ⟨ha,?_,?_⟩
  · have hmul:=mul_le_mul_of_nonneg_left ha hcm.le
    have hterm:1/4≤(c-1)*(1/(3*c)):=by
      have h3:0<3*c:=by positivity
      have hh:(1/4:ℝ)≤(c-1)/(3*c):=by
        apply (le_div_iff₀ h3).2
        nlinarith
      simpa [div_eq_mul_inv] using hh
    dsimp [b]
    have hf0:=mul_nonneg hθ1 hf
    linarith
  · dsimp [a,t]
    have hℓnon:0≤ℓ:=by linarith
    have hfactor:1-θ≤1:=by linarith
    have hh:(1-θ)*ℓ≤1:=by
      have h1:=mul_le_mul_of_nonneg_right hfactor hℓnon
      nlinarith
    have hdiv:=div_le_div_of_nonneg_right hh hc0.le
    simpa using hdiv
end Oberwolfach
