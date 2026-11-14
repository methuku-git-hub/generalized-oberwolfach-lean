module

public import Oberwolfach.FiniteWindowGeometricBounds

@[expose] public section
/-! Bound the cumulative cost of a finite recent window by the current
    level size and the worst geometric ratio across that window. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_recent_window_card_le (i buffer:ℕ) (hbuffer:2≤buffer):
    (Finset.Icc (i+2-buffer) i).card≤buffer :=by
  rw [Nat.card_Icc]
  omega

theorem finite_recent_window_cost_bound
    (a cost:ℕ→ℝ) (K rate C:ℝ) (i buffer:ℕ) (hbuffer:2≤buffer)
    (hK:1≤K) (hrate:0≤rate) (hC:0≤C) (ha:0≤a i)
    (hstep:∀j < i,a j≤K*a (j+1))
    (hcost:∀j∈Finset.Icc (i+2-buffer) i,cost j≤rate*a j+C):
    ∑j∈Finset.Icc (i+2-buffer) i,cost j≤
      (buffer:ℝ)*(rate*K^(buffer-2)*a i+C) :=by
  let J:=Finset.Icc (i+2-buffer) i
  have hcard:(J.card:ℝ)≤buffer:=by exact_mod_cast finite_recent_window_card_le i buffer hbuffer
  have hbound:∀j∈J,cost j≤rate*K^(buffer-2)*a i+C:=by
    intro j hj
    have hjbounds:=Finset.mem_Icc.mp hj
    have hdist:i-j≤buffer-2:=by omega
    have hpow:K^(i-j)≤K^(buffer-2):=pow_le_pow_right₀ hK hdist
    have hprev:=finite_window_step_power_bound a K i (by linarith) hstep j hjbounds.2
    have hscale:=mul_le_mul_of_nonneg_right hpow ha
    have hrate':=mul_le_mul_of_nonneg_left (hprev.trans hscale) hrate
    have hc:=hcost j hj
    nlinarith only [hc,hrate']
  have hcoef:0≤rate*K^(buffer-2)*a i+C:=by positivity
  exact finite_window_sum_uniform_bound J cost _ _ hcoef (by positivity) hcard hbound
end Oberwolfach
