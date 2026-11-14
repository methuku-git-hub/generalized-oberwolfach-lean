module

public import Oberwolfach.OrdinaryReservedBlockCapacity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
/-! Fourth-root size condition for reserved blocks at a hub whose long
fraction may be much smaller than one half. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_capacity_from_rpow
    {I:Type} [Fintype I] (a:I→ℕ) (c d K demand:ℕ) (N ell ell0 θ:ℝ)
    (hc:0<c) (hd:0<d) (hK:0<K) (hN:0<N) (hθ:0<θ) (hell0:0<ell0) (hell:ell0≤ell)
    (hmin:∀i,K≤a i) (htotal:((∑i,a i:ℕ):ℝ)=ell*N)
    (hcut:5/((c:ℝ)*(d:ℝ)+5)+(c:ℝ)*(d:ℝ)/K≤θ/2)
    (hlarge:4*(c:ℝ)/(θ*ell0)<N^((1:ℝ)/4))
    (hdemand:(demand:ℝ)≤(1-θ)*ell*N/((c:ℝ)*(d:ℝ))+2*N^((3:ℝ)/4)/(d:ℝ)):
    demand≤∑i,a i/(c*d+5) :=by
  let x:=N^((1:ℝ)/4)
  have hx:0<x:=Real.rpow_pos_of_pos hN _
  have h4:x^4=N:=by
    dsimp [x]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num
  have h3:x^3=N^((3:ℝ)/4):=by
    dsimp [x]
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num
  have hcR:0<(c:ℝ):=by exact_mod_cast hc
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hscale:4*(c:ℝ)<θ*ell0*x:=by
    have hh:=(div_lt_iff₀ (mul_pos hθ hell0)).mp hlarge
    simpa only [x,mul_comm,mul_left_comm,mul_assoc] using hh
  have hp:=mul_lt_mul_of_pos_right hscale (pow_pos hx 3)
  have herr:2*N^((3:ℝ)/4)/(d:ℝ)<θ*ell0*N/(2*((c*d:ℕ):ℝ)):=by
    rw [←h3,←h4]
    push_cast
    apply (div_lt_div_iff₀ hdR (by positivity : 0<2*((c:ℝ)*d))).2
    nlinarith [hp]
  apply ordinary_reserved_block_capacity a (c*d) K demand N ell ell0 θ (2*N^((3:ℝ)/4)/(d:ℝ))
    (Nat.mul_pos hc hd) hK hN.le hθ hell0 hell hmin htotal
  · simpa only [Nat.cast_mul] using hcut
  · exact herr
  · simpa only [Nat.cast_mul] using hdemand
end Oberwolfach
