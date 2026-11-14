module

public import Oberwolfach.TriangleDenseTransformerConstruction

@[expose] public section
/-! Explicit inequalities for fixing the triangle transformer's small
spoke error before the bounded root complexity. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem triangle_budgets_from_uniform_root_bounds
    (β ε:ℝ) (q n m w r e t d b:ℕ)
    (hβ:0<β) (hβ1:β≤1) (hε:0≤ε) (hεsmall:ε≤β/64)
    (hn:64*(11*(q:ℝ)+1)≤β*n) (hm:4*q+1≤m)
    (hw:w≤q) (hr:r≤q) (he:e≤q) (ht:t≤q) (hd:d≤q) (hb:b≤q):
    ε≤β ∧
    ((w+r+e+2*t+1:ℕ):ℝ)<2*β*n ∧
    ((b+e:ℕ):ℝ)<(1-9*ε)*m ∧
    2*ε*n+((w+2*(e+t)+6*d:ℕ):ℝ)≤(β/4)*n :=by
  have hq:0≤(q:ℝ):=by positivity
  have hn0:0≤(n:ℝ):=by positivity
  have hm0:0≤(m:ℝ):=by positivity
  have hw':(w:ℝ)≤q:=Nat.cast_le.mpr hw
  have hr':(r:ℝ)≤q:=Nat.cast_le.mpr hr
  have he':(e:ℝ)≤q:=Nat.cast_le.mpr he
  have ht':(t:ℝ)≤q:=Nat.cast_le.mpr ht
  have hd':(d:ℝ)≤q:=Nat.cast_le.mpr hd
  have hb':(b:ℝ)≤q:=Nat.cast_le.mpr hb
  have hm':4*(q:ℝ)+1≤m:=by exact_mod_cast hm
  have hen:ε*(n:ℝ)≤(β/64)*(n:ℝ):=mul_le_mul_of_nonneg_right hεsmall hn0
  have hem:ε*(m:ℝ)≤(β/64)*(m:ℝ):=mul_le_mul_of_nonneg_right hεsmall hm0
  have hbm:(β:ℝ)*(m:ℝ)≤m:=by nlinarith
  constructor
  · linarith
  constructor
  · push_cast
    nlinarith
  constructor
  · push_cast
    nlinarith
  · push_cast
    nlinarith
end Oberwolfach
