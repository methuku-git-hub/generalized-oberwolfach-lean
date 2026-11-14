module

public import Oberwolfach.FirstVortexMatchingJointMargins

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_incidence_margin
    (d:ℕ) (lam a γ:ℝ) (hd:3≤d) (hlam:0≤lam)
    (ha:a≤lam/(10*d)) (hγ:γ≤lam/(10*d)):
    2*max a (4*γ)≤lam/3:=by
  have hdR:(3:ℝ)≤d:=by exact_mod_cast hd
  have hdpos:(0:ℝ)<10*(d:ℝ):=by positivity
  have hq:0≤lam/(10*(d:ℝ)):=div_nonneg hlam hdpos.le
  have hm:max a (4*γ)≤4*(lam/(10*(d:ℝ))):=max_le (by linarith) (by linarith)
  have hb:4*(lam/(10*(d:ℝ)))≤lam/6:=by
    have heq:4*(lam/(10*(d:ℝ)))=(4*lam)/(10*(d:ℝ)):=by ring
    rw [heq]
    apply (div_le_iff₀ hdpos).2
    have hh:=mul_nonneg hlam (show (0:ℝ)≤(d:ℝ)-3 by linarith)
    field_simp
    nlinarith only [hh,hlam]
  linarith
end Oberwolfach
