module

public import Oberwolfach.HubTestMassMargin

@[expose] public section
/-! The sharper relative errors recover the manuscript's one-half test-mass
constant while retaining the same fixed weights and hub counts. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem hub_test_mass_manuscript_margin
    (n s η f fmin θ τ err card r rmax mass:ℝ)
    (hn:0≤n) (hs:0<s) (hη:0≤η) (hf:fmin≤f) (hfmin:0≤fmin)
    (hθ:θ≤1/10) (hτ:τ≤1/16) (herr:err≤η/16)
    (hcount:(15/16:ℝ)*s*n≤card) (hr:0<r) (hrmax:r≤rmax)
    (hbalance:η*s=(1-θ)*f)
    (hmass:((1-τ)*η-err)*card/r≤mass):
    fmin*n/(2*rmax)≤mass :=by
  have hapos:(7/8:ℝ)*η≤(1-τ)*η-err:=by nlinarith
  have hcard:0≤card:=le_trans (by positivity) hcount
  have hprod: ((7/8:ℝ)*η)*((15/16:ℝ)*s*n)≤((1-τ)*η-err)*card :=
    mul_le_mul hapos hcount (by positivity) (le_trans (by positivity) hapos)
  have hθpos:(9/10:ℝ)≤1-θ:=by linarith
  have hfpos:0≤f:=le_trans hfmin hf
  have hfn:(9/10:ℝ)*fmin*n≤(1-θ)*f*n:=by
    have h1:0≤(f-fmin)*n:=mul_nonneg (sub_nonneg.mpr hf) hn
    have h2:0≤((1-θ)-9/10)*(f*n):=mul_nonneg (sub_nonneg.mpr hθpos) (mul_nonneg hfpos hn)
    nlinarith
  have hbalanceN:=congrArg (fun x:ℝ=>x*n) hbalance
  have hrmaxpos:0<rmax:=lt_of_lt_of_le hr hrmax
  have hnum:fmin*n/2≤((1-τ)*η-err)*card:=by
    nlinarith [hprod,hfn,hbalanceN]
  have hdiv:fmin*n/(2*rmax)≤((1-τ)*η-err)*card/r := by
    apply (div_le_div_iff₀ (by positivity : 0<2*rmax) hr).2
    have hh:=mul_le_mul_of_nonneg_right hnum hrmaxpos.le
    have hx:=mul_le_mul_of_nonneg_left hrmax (by positivity : 0≤fmin*n)
    nlinarith
  exact hdiv.trans hmass
end Oberwolfach
