module

public import Mathlib.Tactic

@[expose] public section
/-! Choose the total inner correction budget from small outer loss and
sublinear errors, without comparing the global loss with the local cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_margins
    (N I ε c rho eta t ζ B outer q:ℝ)
    (hN:0<N) (hI:0≤I) (hIN:I≤N) (hε:0≤ε) (hc:0≤c) (hrho:0≤rho) (heta:0≤eta) (ht:0≤t)
    (hsize:ε*N/2≤I) (hζ0:0≤ζ) (hB0:0≤B) (houter0:0≤outer) (hq0:0≤q)
    (hζ:ζ≤t) (hB:B≤t*N) (houter:outer≤t*N) (hq:q≤t*N)
    (hglobal:5*t≤ε*eta/2) (hlocal:5*t≤c*rho*ε/8):
    ∃lossInside inside:ℝ,0≤lossInside ∧ 0≤ inside ∧
      I*(ζ*N+2*B)+N*outer≤lossInside ∧ I*q+lossInside≤ inside ∧
      inside≤I*eta*N ∧ inside≤c*rho*N*I/4 :=by
  let lossInside:=I*(ζ*N+2*B)+N*outer
  let inside:=I*q+lossInside
  have htn:0≤t*N:=mul_nonneg ht hN.le
  have hItn:I*(t*N)≤N*(t*N):=mul_le_mul_of_nonneg_right hIN htn
  have hζN:=mul_le_mul_of_nonneg_right hζ hN.le
  have h1:=mul_le_mul_of_nonneg_left hζN hI
  have h2:=mul_le_mul_of_nonneg_left hB hI
  have h3:=mul_le_mul_of_nonneg_left houter hN.le
  have h4:=mul_le_mul_of_nonneg_left hq hI
  have htotal:inside≤5*t*N^2:=by dsimp [inside,lossInside];nlinarith
  have hN2:0≤N^2:=sq_nonneg N
  have hg:=mul_le_mul_of_nonneg_right hglobal hN2
  have hl:=mul_le_mul_of_nonneg_right hlocal hN2
  have hscaleG:=mul_le_mul_of_nonneg_left hsize (mul_nonneg heta hN.le)
  have hscaleL:=mul_le_mul_of_nonneg_left hsize (mul_nonneg (mul_nonneg hc hrho) hN.le)
  have hG:inside≤I*eta*N:=by nlinarith [htotal,hg,hscaleG]
  have hL:inside≤c*rho*N*I/4:=by nlinarith [htotal,hl,hscaleL]
  refine ⟨lossInside,inside,?_,?_,le_rfl,by dsimp [inside];linarith,hG,hL⟩
  · dsimp [lossInside];positivity
  · dsimp [inside,lossInside];positivity
end Oberwolfach
