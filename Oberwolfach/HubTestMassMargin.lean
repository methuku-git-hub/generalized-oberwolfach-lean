module

public import Oberwolfach.MixedRestrictedHubMass

@[expose] public section
/-! Convert retained spoke-count and root-load margins into a uniform
positive lower bound for a prescribed hub-frequency test. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem hub_test_mass_margin
    (n s η f fmin θ τ err card r rmax mass:ℝ)
    (hn:0≤n) (hs:0<s) (hη:0≤η) (hf: fmin≤f) (hfmin:0≤fmin)
    (hθ:θ≤1/2) (hτ:τ≤1/2) (herr:err≤η/4)
    (hcount:s*n/2≤card) (hr:0<r) (hrmax:r≤rmax)
    (hbalance:η*s=(1-θ)*f)
    (hmass:((1-τ)*η-err)*card/r≤mass):
    fmin*n/(16*rmax)≤mass := by
  have hapos:η/4≤(1-τ)*η-err:=by nlinarith
  have hcard:0≤card:=le_trans (by positivity) hcount
  have hprod: (η/4)*(s*n/2)≤((1-τ)*η-err)*card :=
    mul_le_mul hapos hcount (by positivity) (le_trans (by positivity) hapos)
  have hθpos:(1/2:ℝ)≤1-θ:=by linarith
  have hfpos:0≤f:=le_trans hfmin hf
  have hbal:η*s/2≤η*s:=by nlinarith [mul_nonneg hη hs.le]
  have hfn:fmin*n/2≤(1-θ)*f*n:=by
    have h1:0≤(f-fmin)*n:=mul_nonneg (sub_nonneg.mpr hf) hn
    have h2:0≤((1-θ)-1/2)*(f*n):=mul_nonneg (sub_nonneg.mpr hθpos) (mul_nonneg hfpos hn)
    nlinarith
  have hrmaxpos:0<rmax:=lt_of_lt_of_le hr hrmax
  have hnum:fmin*n/16≤((1-τ)*η-err)*card:=by
    nlinarith [hprod,hfn,hbalance]
  have hdiv:fmin*n/(16*rmax)≤((1-τ)*η-err)*card/r := by
    apply (div_le_div_iff₀ (by positivity : 0<16*rmax) hr).2
    have hh:=mul_le_mul_of_nonneg_right hnum hrmaxpos.le
    have hx:=mul_le_mul_of_nonneg_left hrmax (by positivity : 0≤fmin*n)
    nlinarith
  exact hdiv.trans hmass
end Oberwolfach
