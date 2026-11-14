module

public import Oberwolfach.MarkedVortexInnerUpperSizeInputs

@[expose] public section
/-! Numerical lower bounds for the active vertex and hub domains. The
vortex ratio is chosen before the active density parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_hub_density_arithmetic
    (n nV nU I J T R A B ε ρ ω:ℝ)
    (hn:0≤n) (hnV:0≤nV) (hnU:0≤nU) (hI:0≤I) (hJ:0≤J)
    (he:0<ε) (hehalf:ε≤1/2) (hρ:0<ρ) (hω:0≤ω)
    (hV:nV≤n) (hU:nU≤n) (hIlo:(ε/2)*n≤I) (hJlo:(ρ/8)*I≤J)
    (hT:T≤ε*I) (hR:R≤ε*J) (hA:A=I-T) (hB:B=J-R)
    (hωv:ω≤ε/8) (hωu:ω≤ρ*ε/64):
    ω*(nV+nU)≤A ∧ ω*(nV+nU)≤B:=by
  have hsum:nV+nU≤2*n:=by linarith
  have hAlo:I/2≤A:=by
    rw [hA]
    nlinarith [mul_nonneg (sub_nonneg.mpr hehalf) hI]
  have hBlo:J/2≤B:=by
    rw [hB]
    nlinarith [mul_nonneg (sub_nonneg.mpr hehalf) hJ]
  have hAparent:(ε/4)*n≤A:=by linarith [hIlo,hAlo]
  have hJparent:(ρ*ε/16)*n≤J:=by
    have hh:=mul_le_mul_of_nonneg_left hIlo (show 0≤ρ/8 by positivity)
    nlinarith [hh,hJlo]
  have hBparent:(ρ*ε/32)*n≤B:=by linarith [hJparent,hBlo]
  have hleft:ω*(nV+nU)≤2*ω*n:=by nlinarith [mul_le_mul_of_nonneg_left hsum hω]
  have hrightA:2*ω*n≤(ε/4)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hωv hn
    nlinarith [hh]
  have hrightB:2*ω*n≤(ρ*ε/32)*n:=by
    have hh:=mul_le_mul_of_nonneg_right hωu hn
    nlinarith [hh]
  exact ⟨hleft.trans (hrightA.trans hAparent),hleft.trans (hrightB.trans hBparent)⟩
end Oberwolfach
