module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! The early deletion tolerance selected below the matching error is small
for the later precise-degree estimate, without changing the matching event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_early_deletion_rate_bound
    (lam θ eps ζ:ℝ) (K:ℕ) (hlam:0≤lam) (hθ:θ≤1) (hK:1≤K)
    (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hζ:ζ≤eps/8):
    ζ≤lam/3 :=by
  have hK1:(1:ℝ)≤K:=by exact_mod_cast hK
  have hden:1≤100*(K:ℝ)^2:=by nlinarith [sq_nonneg ((K:ℝ)-1)]
  have hratio:θ/(100*(K:ℝ)^2)≤1:=by
    apply (div_le_one (by positivity:0<100*(K:ℝ)^2)).2
    linarith
  have hmul:=mul_le_mul_of_nonneg_left hratio hlam
  nlinarith only [heps,hζ,hmul,hlam]
end Oberwolfach
