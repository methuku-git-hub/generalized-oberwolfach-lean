module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! Fixed spacing and sublinear sampling errors fit the later inner-sum
rates uniformly for large hosts. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_finite_errors
    (d:ℕ) (s t:ℝ) (hs:0<s) (ht:0<t):
    ∃N:ℕ,∀n:ℕ,N≤n→
      ((6*d+2:ℕ):ℝ)≤s*n ∧ 1≤s*n ∧
      (n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)≤t*n :=by
  have hmin:0<min s t:=lt_min hs ht
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error ((d:ℝ)+1) ((6*d+3:ℕ):ℝ) 1 (2/5) (min s t)
    (by positivity) (by positivity) (by norm_num) (by norm_num) hmin
  refine ⟨N,?_⟩
  intro n hn
  have hpow:(n:ℝ)^(3/5:ℝ)≤1*(n:ℝ)^(1-(2/5:ℝ)):=by norm_num
  have hh:=hN n hn ((n:ℝ)^(3/5:ℝ)) hpow
  have hN0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hsN:=mul_le_mul_of_nonneg_right (min_le_left s t) hN0
  have htN:=mul_le_mul_of_nonneg_right (min_le_right s t) hN0
  have hp:0≤(n:ℝ)^(3/5:ℝ):=by positivity
  have hd:(0:ℝ)≤d:=Nat.cast_nonneg _
  push_cast at hh ⊢
  constructor
  · nlinarith [mul_nonneg hd hp]
  constructor
  · nlinarith [mul_nonneg hd hp]
  · nlinarith
end Oberwolfach
