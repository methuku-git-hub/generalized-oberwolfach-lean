module

public import Oberwolfach.FirstVortexMatchingRates

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_deletion_rate_margin
    (K:ℕ) (θ lam eps ξ:ℝ) (hK:1≤K) (hθ:0≤θ) (hθ1:θ≤1)
    (hlam:0≤lam) (heps:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2):
    ξ≤lam/3:=by
  have hKR:(1:ℝ)≤K:=by exact_mod_cast hK
  have hK2:(1:ℝ)≤(K:ℝ)^2:=by nlinarith only [hKR]
  have hden:(0:ℝ)<100*(K:ℝ)^2:=by positivity
  have hfrac:θ/(100*(K:ℝ)^2)≤1:=by
    apply (div_le_iff₀ hden).2
    nlinarith only [hK2,hθ1]
  have hh:=mul_le_mul_of_nonneg_left hfrac hlam
  nlinarith only [hh,heps,hξ,hlam]
end Oberwolfach
