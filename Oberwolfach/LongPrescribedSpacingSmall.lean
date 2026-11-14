module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The actual prescribed set bound becomes arbitrarily small by choosing
spacing after the first-vortex size and then taking the host large. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem long_prescribed_spacing_eventually_small
    (d:ℕ) (η:ℝ) (hd:0<d) (hη:0<η) (hspacing:1/(d:ℝ)≤η/10):
    ∃N:ℕ,∀n:ℕ,N≤n→∀a γ:ℝ,max a γ≤1/(10*(d:ℝ))→
      2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n≤η*n :=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error (4/(d:ℝ)) 0 1 (1/4) (η/2)
    (by positivity) (by norm_num) (by norm_num) (by norm_num) (by positivity)
  refine ⟨N,?_⟩
  intro n hn a γ hdefect
  have herr:=hN n hn ((n:ℝ)^(3/4:ℝ)) (by norm_num)
  have hcoeff:2/(d:ℝ)+2*max a γ≤η/2:=by
    have hh:1/(10*(d:ℝ))=(1/(d:ℝ))/10:=by ring
    have htwo:2/(d:ℝ)=2*(1/(d:ℝ)):=by ring
    rw [hh] at hdefect
    nlinarith only [hspacing,hdefect,htwo,hη]
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hlinear:=mul_le_mul_of_nonneg_right hcoeff hn0
  have heq:2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n=
      (2/(d:ℝ)+2*max a γ)*n+(4/(d:ℝ))*(n:ℝ)^(3/4:ℝ):=by field_simp;ring
  rw [heq]
  linarith
end Oberwolfach
