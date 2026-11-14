module

public import Oberwolfach.FloorOrbit

@[expose] public section
/-! A positive floor orbit controls any fixed earlier level by a fixed
multiple of its current size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem floorOrbit_previous_le_ratio {ε:ℝ} (he:0<ε) (he1:ε≤1) (n i:ℕ)
    (hi:0<floorOrbit ε n i):
    (floorOrbit ε n (i-1):ℝ)≤(2/ε)*(floorOrbit ε n i) :=by
  by_cases hz:i=0
  · subst i
    simp only [Nat.zero_sub,floorOrbit_zero]
    have hn:0≤(n:ℝ):=by positivity
    have hcoef:1≤2/ε:=(le_div_iff₀ he).mpr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hcoef hn]
  · have his:i-1+1=i:=by omega
    have hh:=Nat.lt_floor_add_one (ε*(floorOrbit ε n (i-1):ℝ))
    rw [←floorOrbit_succ,his] at hh
    have hpos:(1:ℝ)≤floorOrbit ε n i:=by exact_mod_cast (show 1≤floorOrbit ε n i by omega)
    have hbound:ε*(floorOrbit ε n (i-1):ℝ)≤2*floorOrbit ε n i:=by linarith
    have hdiv:((floorOrbit ε n (i-1):ℝ)≤(2*(floorOrbit ε n i))/ε):=(le_div_iff₀ he).mpr (by nlinarith only [hbound])
    convert hdiv using 1 <;> ring

theorem floorOrbit_lookback_le_ratio {ε:ℝ} (he:0<ε) (he1:ε<1) (n i k:ℕ)
    (hi:0<floorOrbit ε n i):
    (floorOrbit ε n (i-k):ℝ)≤(2/ε)^k*(floorOrbit ε n i) :=by
  induction k with
  | zero => simp
  | succ k ih =>
    have hj:i-k ≤ i:=by omega
    have hpos:0<floorOrbit ε n (i-k):=lt_of_lt_of_le hi (floorOrbit_antitone he1 n hj)
    have hprev:=floorOrbit_previous_le_ratio he he1.le n (i-k) hpos
    have hmul:=mul_le_mul_of_nonneg_left ih (show 0≤2/ε by positivity)
    have hsub:i-(k+1)=(i-k)-1:=by omega
    rw [hsub]
    calc
      (floorOrbit ε n ((i-k)-1):ℝ)≤(2/ε)*(floorOrbit ε n (i-k)):=hprev
      _≤(2/ε)*((2/ε)^k*floorOrbit ε n i):=hmul
      _=(2/ε)^(k+1)*floorOrbit ε n i:=by rw [pow_succ];ring
end Oberwolfach
