module

public import Oberwolfach.FirstVortexResidualMatchingAlphaChoice

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_residual_target_coefficient
    (d:ℕ) (hd:0<d) (θ ρ₀ ε η ζ lam a γ:ℝ)
    (hθ:0<θ) (hρ₀:ρ₀≤1) (hε:ε≤(ρ₀/4)/80000)
    (hη:η≤θ/4096) (hζ:ζ≤θ/4096)
    (hlam:0≤lam) (hlam1:lam≤1) (hinv:1/(d:ℝ)≤θ/1024)
    (ha:a≤lam/(10*(d:ℝ))) (hγ:γ≤lam/(10*(d:ℝ))):
    2*θ*ε+η+ζ+max a γ≤θ/1024 :=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hθ0:0≤θ:=hθ.le
  have hεsmall:ε≤1/320000:=by linarith
  have hproduct:2*θ*ε≤θ/4096:=by nlinarith [mul_nonneg (show 0≤1/320000-ε by linarith) hθ0]
  have hscale:lam*(1/(d:ℝ))≤1/(d:ℝ):=by nlinarith [mul_nonneg (show 0≤1-lam by linarith) (show 0≤1/(d:ℝ) by positivity)]
  have hdiv:lam/(10*(d:ℝ))≤θ/4096:=by
    have heq:lam/(10*(d:ℝ))=lam*(1/(d:ℝ))/10:=by ring
    nlinarith
  have hmax:max a γ≤θ/4096:=max_le (ha.trans hdiv) (hγ.trans hdiv)
  linarith
end Oberwolfach
