module

public import Oberwolfach.OrdinaryReservoirErrorEventuallySmall

@[expose] public section
/-! The explicit absorber/correction failure terms fit an arbitrary
positive allowance while retaining the original n^-10 tail. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reservoir_failure_budget
    (δ:ℝ) (hδ:0<δ):
    ∃N:ℕ,1 ≤ N ∧ ∀n:ℕ,N ≤ n  → 
      2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2) ≤ δ+1/(n:ℝ)^10 :=by
  obtain ⟨N,hN⟩:=exists_nat_gt (4/δ)
  refine ⟨max N 1,by omega,?_⟩
  intro n hn
  have hn1:(1:ℝ) ≤ n:=by exact_mod_cast (show 1 ≤ n by omega)
  have hn0:(0:ℝ)<n:=by linarith
  have hNn:(N:ℝ) ≤ n:=by exact_mod_cast (show N ≤ n by omega)
  have hpow:(n:ℝ) ≤ (n:ℝ)^10:=by
    have hh:=pow_le_pow_right₀ hn1 (show (1:ℕ) ≤ 10 by omega)
    simpa using hh
  have hinv10:1/(n:ℝ)^10 ≤ 1/(n:ℝ):=one_div_le_one_div_of_le hn0 hpow
  have hinv2:1/(n:ℝ)^2 ≤ 1/(n:ℝ):=by
    apply one_div_le_one_div_of_le hn0
    nlinarith only [hn1]
  have hfour:4/(n:ℝ)<δ:=by
    have hh:4/δ<(n:ℝ):=hN.trans_le hNn
    have hh':4<δ*(n:ℝ):=by simpa [mul_comm] using (div_lt_iff₀ hδ).mp hh
    exact (div_lt_iff₀ hn0).mpr (by nlinarith only [hh'])
  have h2ten:2/(n:ℝ)^10=2*(1/(n:ℝ)^10):=by ring
  have h2sq:2/(n:ℝ)^2=2*(1/(n:ℝ)^2):=by ring
  have hf:4*(1/(n:ℝ))<δ:=by simpa only [div_eq_mul_inv,one_mul] using hfour
  rw [h2ten,h2sq]
  linarith only [hinv10,hinv2,hf]
end Oberwolfach
