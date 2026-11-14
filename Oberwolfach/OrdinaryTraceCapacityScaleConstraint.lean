module

public import Oberwolfach.OrdinaryCleanupCapacityQuadraticRate
public import Oberwolfach.OrdinaryVortexBufferedCostGeometry

@[expose] public section
/-! Necessary rate constraints for the current protected-trace and capacity interfaces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_cleanup_cost_requires_trace_rate
    (N Kcap Dmax m:ℕ) (p ν η rate:ℝ) (hN:0<N) (hν:0≤ν) (hη:0≤η)
    (hcost:ν*N+η*N+2*((2*p)*N)+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*N):
    4*p≤rate :=by
  have hN':(0:ℝ)<N:=by exact_mod_cast hN
  have hother:0≤ν*N+η*N+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ):=by positivity
  by_contra h
  have hh:0<(4*p-rate)*(N:ℝ):=mul_pos (by linarith) hN'
  nlinarith only [hcost,hother,hh]

theorem ordinary_trace_rate_decay (δ ε K rate:ℝ) (buffer:ℕ)
    (hδ:0≤δ) (hε:0<ε) (hK:2/ε≤K)
    (hrate:rate≤δ/(32*((buffer:ℝ)+1)*K^buffer)):
    rate≤δ*(ε/2)^buffer :=by
  have hKpos:0<K:=lt_of_lt_of_le (by positivity:0<2/ε) hK
  have hKpow:0<K^buffer:=pow_pos hKpos _
  have hden:K^buffer≤32*((buffer:ℝ)+1)*K^buffer:=by
    have hh:(1:ℝ)≤32*((buffer:ℝ)+1):=by
      have ht:(0:ℝ)≤buffer:=by positivity
      nlinarith only [ht]
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) hKpow.le]
  have hrate':rate≤δ/(K^buffer):=hrate.trans (div_le_div_of_nonneg_left hδ hKpow hden)
  have hinv:1/K≤ε/2:=by
    apply (div_le_iff₀ hKpos).mpr
    have hh:2≤K*ε:=(div_le_iff₀ hε).mp hK
    nlinarith only [hh]
  have hpow:(1/K)^buffer≤(ε/2)^buffer:=pow_le_pow_left₀ (by positivity) hinv _
  have hmul:=mul_le_mul_of_nonneg_left hpow hδ
  have heq:δ/(K^buffer)=δ*(1/K)^buffer:=by rw [one_div_pow];ring
  rw [heq] at hrate'
  exact hrate'.trans hmul

theorem ordinary_quadratic_sampling_exceeds_twenty_eighth_trace_budget
    (a C:ℝ) (ha:0<a) (hC:0<C):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε δ rate:ℝ,0<ε→ε≤εcap→
      δ≤C*ε^28→ rate≤δ → ¬(4*(a*ε^2)≤rate) :=by
  let εcap:ℝ:=min 1 (a/(C+1))
  have hcap:0<εcap:=by dsimp [εcap];positivity
  refine ⟨εcap,hcap,min_le_left _ _,?_⟩
  intro ε δ rate hε he hδ hrate hreq
  have he1:ε≤1:=he.trans (min_le_left _ _)
  have heA:ε≤a/(C+1):=he.trans (min_le_right _ _)
  have hcoef:C*ε≤a:=by
    have hh:ε*(C+1)≤a:=(le_div_iff₀ (by positivity:0<C+1)).mp heA
    nlinarith only [hh,hε]
  have he28:ε^28≤ε^3:=by
    have hh:=mul_le_mul_of_nonneg_right (show ε^25≤1 from pow_le_one₀ hε.le he1) (show 0≤ε^3 by positivity)
    nlinarith only [hh]
  have hbound:C*ε^28≤a*ε^2:=by
    have hh:=mul_le_mul_of_nonneg_left he28 hC.le
    have hh':=mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)
    nlinarith only [hh,hh']
  have haε:0<a*ε^2:=by positivity
  nlinarith only [hδ,hrate,hreq,hbound,haε]

end Oberwolfach
