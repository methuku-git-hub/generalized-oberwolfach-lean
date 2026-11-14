module

public import Mathlib.Tactic

@[expose] public section
/-! The manuscript's matching and deletion tolerances supply the numerical
incidence bounds used by the class-specific assignment. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_class_matching_incidence_margins
    (K d:ℕ) (hK:1≤K) (hd:3≤d) (lam θ eps ξ a γ:ℝ)
    (hlam:0≤lam) (hθ:θ≤1) (ha0:0≤a) (hγ0:0≤γ)
    (ha:a≤lam/(10*d)) (hγ:γ≤lam/(10*d))
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2):
    2*max a (4*γ)≤lam/3 ∧ ξ≤lam/3:=by
  have hdR:3≤(d:ℝ):=by exact_mod_cast hd
  have hKR:1≤(K:ℝ):=by exact_mod_cast hK
  have hden:0<10*(d:ℝ):=by positivity
  have ha1:10*(d:ℝ)*a≤lam:=by simpa [mul_comm] using (le_div_iff₀ hden).1 ha
  have hg1:10*(d:ℝ)*γ≤lam:=by simpa [mul_comm] using (le_div_iff₀ hden).1 hγ
  have ha2:30*a≤lam:=by nlinarith [mul_nonneg (show 0≤(d:ℝ)-3 by linarith) ha0]
  have hg2:30*γ≤lam:=by nlinarith [mul_nonneg (show 0≤(d:ℝ)-3 by linarith) hγ0]
  have hKsq:1≤(K:ℝ)^2:=by nlinarith
  have hf:θ/(100*(K:ℝ)^2)≤1/100:=by
    apply (div_le_iff₀ (by positivity : 0<100*(K:ℝ)^2)).2
    nlinarith
  have hmul:=mul_le_mul_of_nonneg_left hf hlam
  have he:3*eps≤lam/100:=by nlinarith only [heps,hmul]
  constructor
  · have hm:max a (4*γ)≤lam/6:=max_le (by linarith) (by linarith)
    linarith
  · linarith
end Oberwolfach
