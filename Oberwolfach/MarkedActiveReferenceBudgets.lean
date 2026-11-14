module

public import Mathlib.Tactic

@[expose] public section

/-! The global reference estimates use one deletion scale. Every inequality
below is uniform in the graph orders; the scale is chosen before those
orders, the separation radius and any later sampling probability. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Oberwolfach

theorem marked_active_reference_budget_from_scale
    (r h:ℕ) (n nA mA omega gamma p p0 beta epsA deltaSp eta0 Bbar kappa:ℝ)
    (hn:0<n) (hnA:n/2≤nA) (hmA:omega*n/2≤mA)
    (ho:0<omega) (hg:0≤gamma) (hp0:0≤p0) (hp:p0≤p)
    (hB:0≤Bbar) (hk:0≤kappa)
    (hdeg:8*kappa≤epsA) (htwo:3*kappa≤gamma*p0^2)
    (hconf:8*(r+5:ℝ)*kappa≤12*beta)
    (hhubs:(1+2*(r+5:ℝ))*kappa≤28*beta)
    (hrow:2*(2+2*(h:ℝ))*kappa≤deltaSp)
    (hidx:2*(2+(h:ℝ))*kappa≤deltaSp*p0^2*omega)
    (hseed:(1+2*(r+5:ℝ)^3*Bbar+66*(r+5:ℝ)^4*Bbar)*kappa≤eta0)
    (errR errI removedR removedU delta zetaOld eta:ℝ)
    (heR:errR≤kappa*n) (heI:errI≤kappa*n)
    (hR:removedR≤kappa*n) (hU:removedU≤kappa*n)
    (hd:delta≤kappa*n) (hd0:0≤delta)
    (hz:zetaOld≤kappa) (he:eta≤kappa):
    errR+removedR+delta+removedU≤epsA*nA∧
    removedR+2*delta≤gamma*p^2*n∧
    2*(r+5:ℝ)*(removedR+zetaOld*n)+4*(r+5:ℝ)*delta≤12*beta*n∧
    removedU+(r+5:ℝ)*(delta+zetaOld*n)≤28*beta*n∧
    errR+removedR+h*(delta+delta)≤deltaSp*nA∧
    errI+removedU+h*delta≤deltaSp*p0^2*mA∧
    eta+(removedR+removedU)*(r+5:ℝ)^3*Bbar/n+
      11*(r+5:ℝ)^4*Bbar*(2*delta+delta)/nA≤eta0:=by
  have hn0:=hn.le
  have hnA0:0<nA:=lt_of_lt_of_le (by positivity) hnA
  have heps:0≤epsA:=le_trans (by positivity) hdeg
  have hsp:0≤deltaSp:=le_trans (by positivity) hrow
  have hzN:=mul_le_mul_of_nonneg_right hz hn0
  have hp2:p0^2≤p^2:=pow_le_pow_left₀ hp0 hp 2
  have htwoN:=mul_le_mul_of_nonneg_right htwo hn0
  have hp2N:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hg) hn0
  have hconfN:=mul_le_mul_of_nonneg_right hconf hn0
  have hhubN:=mul_le_mul_of_nonneg_right hhubs hn0
  have hepsN:=mul_le_mul_of_nonneg_right hdeg hn0
  have hepsA:=mul_le_mul_of_nonneg_left hnA heps
  have hrowN:=mul_le_mul_of_nonneg_right hrow hn0
  have hrowA:=mul_le_mul_of_nonneg_left hnA hsp
  have hidxN:=mul_le_mul_of_nonneg_right hidx hn0
  have hidxA:=mul_le_mul_of_nonneg_left hmA (mul_nonneg hsp (sq_nonneg p0))
  have hc:0≤(r+5:ℝ):=by positivity
  have hh:0≤(h:ℝ):=by positivity
  have hconfR:=mul_le_mul_of_nonneg_left (add_le_add hR hzN) (show 0≤2*(r+5:ℝ) by positivity)
  have hconfD:=mul_le_mul_of_nonneg_left hd (show 0≤4*(r+5:ℝ) by positivity)
  have hhubD:=mul_le_mul_of_nonneg_left (add_le_add hd hzN) hc
  have hrowD:=mul_le_mul_of_nonneg_left (add_le_add hd hd) hh
  have hidxD:=mul_le_mul_of_nonneg_left hd hh
  refine ⟨by nlinarith only [heR,hR,hd,hU,hepsN,hepsA],
    by linarith only [hR,hd,htwoN,hp2N],
    by nlinarith only [hconfR,hconfD,hconfN],
    by nlinarith only [hU,hhubD,hhubN],
    by nlinarith only [heR,hR,hrowD,hrowN,hrowA],
    by nlinarith only [heI,hU,hidxD,hidxN,hidxA],?_⟩
  have hratio:(removedR+removedU)/n≤2*kappa:=by
    apply (div_le_iff₀ hn).mpr
    linarith only [hR,hU]
  have hdratio:(2*delta+delta)/nA≤6*kappa:=by
    apply (div_le_iff₀ hnA0).mpr
    have hka:=mul_le_mul_of_nonneg_left hnA hk
    nlinarith only [hd,hka]
  have ha:=mul_le_mul_of_nonneg_right hratio (show 0≤(r+5:ℝ)^3*Bbar by positivity)
  have hb:=mul_le_mul_of_nonneg_left hdratio (show 0≤11*(r+5:ℝ)^4*Bbar by positivity)
  have ha':(removedR+removedU)*(r+5:ℝ)^3*Bbar/n≤2*kappa*((r+5:ℝ)^3*Bbar):=by
    convert ha using 1 <;> ring
  have hb':11*(r+5:ℝ)^4*Bbar*(2*delta+delta)/nA≤11*(r+5:ℝ)^4*Bbar*(6*kappa):=by
    convert hb using 1 <;> ring
  nlinarith only [he,ha',hb',hseed]

end Oberwolfach
