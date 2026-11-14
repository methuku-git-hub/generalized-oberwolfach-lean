module

public import Oberwolfach.OrdinarySameSampleReservoirUniformEditWeights

@[expose] public section
/-! With exponent one, the explicit finite-size reservoir error is
uniformly small once the ambient graph is sufficiently large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reservoir_error_eventually_small
    (lossE χ:ℝ) (hmargin:lossE+χ<1):
    ∃N:ℕ,1 ≤ N ∧ ∀n:ℕ,N ≤ n  → 
      0<1-lossE-2/(n:ℝ)-(1/(n:ℝ)+2/(n:ℝ)^2)-χ :=by
  let margin:ℝ:=1-lossE-χ
  have hm:0<margin:=by dsimp [margin];linarith
  obtain ⟨N,hN⟩:=exists_nat_gt (5/margin)
  refine ⟨max N 1,by omega,?_⟩
  intro n hn
  have hn1:(1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos:(0:ℝ)<n:=by linarith
  have hNn:(N:ℝ) ≤ n:=by exact_mod_cast (show N ≤ n by omega)
  have h5:5<margin*(n:ℝ):=by
    have hh:5<margin*(N:ℝ):=by
      have hh':=(div_lt_iff₀ hm).mp hN
      nlinarith only [hh']
    nlinarith [mul_le_mul_of_nonneg_left hNn hm.le]
  have hratio:2/(n:ℝ)^2 ≤ 2/(n:ℝ):=by
    apply (div_le_div_iff₀ (by positivity) hnpos).2
    nlinarith only [hn1]
  have hsmall:5/(n:ℝ)<margin:=(div_lt_iff₀ hnpos).2 (by nlinarith only [h5])
  have heq:5/(n:ℝ)=2/(n:ℝ)+1/(n:ℝ)+2/(n:ℝ):=by ring
  rw [heq] at hsmall
  dsimp [margin] at hsmall
  linarith only [hratio,hsmall]
end Oberwolfach
