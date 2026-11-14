module

public import Oberwolfach.BoundaryReservationBalances

@[expose] public section

/-! The six retained degree estimates imply all four near-balance
inequalities, with their original coefficient m in the hub equation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def markedSixDegreeBalance (m:ℕ) (d:Fin 6→ℝ):Fin 4→ℝ:=
  ![d 0+d 1-d 4-d 5,d 2+d 3-d 4-d 5,d 3-d 5,d 4-m*d 5]

def markedSixDegreeCoefficients (m:ℕ):Fin 4→Fin 6→ℝ:=
  ![![1,1,0,0,-1,-1],![0,0,1,1,-1,-1],![0,0,0,1,0,-1],![0,0,0,0,1,-(m:ℝ)]]

theorem markedSixDegreeBalance_sum (m:ℕ) (d:Fin 6→ℝ) (i:Fin 4):
    markedSixDegreeBalance m d i=∑ j,markedSixDegreeCoefficients m i j*d j:=by
  fin_cases i <;> simp [markedSixDegreeBalance,markedSixDegreeCoefficients,Fin.sum_univ_succ] <;> ring

theorem markedSixDegreeCoefficients_bound (m:ℕ) (i:Fin 4):
    (∑ j,|markedSixDegreeCoefficients m i j|)≤m+4:=by
  fin_cases i <;> simp [markedSixDegreeCoefficients,Fin.sum_univ_succ] <;> linarith [Nat.cast_nonneg (α:=ℝ) m]

theorem markedSixDegreeBalance_linear (m:ℕ) (a b:Fin 6→ℝ) (s t:ℝ) (i:Fin 4):
    markedSixDegreeBalance m (fun j=>s*a j+t*b j) i=
      s*markedSixDegreeBalance m a i+t*markedSixDegreeBalance m b i:=by
  fin_cases i <;> simp [markedSixDegreeBalance] <;> ring

theorem marked_reservation_balance_errors (m:ℕ) (a b d:Fin 6→ℝ) (p ε η η':ℝ)
    (hp:0≤p) (hp1:p≤1) (hε:0≤ε) (hη:0≤η) (hη':0≤η') (inner:Bool)
    (h:∀ j,|d j-(if inner then (1-p)*(a j-b j) else a j-p*b j)|≤ε)
    (i:Fin 4) (ha:|markedSixDegreeBalance m a i|≤η) (hb:|markedSixDegreeBalance m b i|≤η'):
    |markedSixDegreeBalance m d i|≤η+η'+(m+4)*ε:=by
  let c:Fin 6→ℝ:=fun j=>if inner then (1-p)*(a j-b j) else a j-p*b j
  have he:|markedSixDegreeBalance m d i-markedSixDegreeBalance m c i|≤(m+4)*ε:=by
    rw [markedSixDegreeBalance_sum,markedSixDegreeBalance_sum]
    exact (weighted_pointwise_error (markedSixDegreeCoefficients m i) d c ε h).trans
      (mul_le_mul_of_nonneg_right (markedSixDegreeCoefficients_bound m i) hε)
  have hc:|markedSixDegreeBalance m c i|≤η+η':=by
    cases inner
    · have hc':c=(fun j=>1*a j+(-p)*b j):=by funext j;dsimp[c];ring
      rw [hc',markedSixDegreeBalance_linear,one_mul]
      have hh:=abs_add_le (markedSixDegreeBalance m a i) ((-p)*markedSixDegreeBalance m b i)
      rw [abs_mul,abs_neg,abs_of_nonneg hp] at hh
      have ht:=mul_le_mul_of_nonneg_left hb hp
      have hs:=mul_le_mul_of_nonneg_right hp1 hη'
      linarith only [hh,ha,ht,hs]
    · have hc':c=(fun j=>(1-p)*a j+(-(1-p))*b j):=by funext j;dsimp[c];ring
      rw [hc',markedSixDegreeBalance_linear]
      have hh:=abs_add_le ((1-p)*markedSixDegreeBalance m a i) ((-(1-p))*markedSixDegreeBalance m b i)
      have hn:0≤1-p:=by linarith
      rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg hn] at hh
      have hta:=mul_le_mul_of_nonneg_left ha hn
      have htb:=mul_le_mul_of_nonneg_left hb hn
      have hsa:=mul_le_mul_of_nonneg_right (show 1-p≤1 by linarith) hη
      have hsb:=mul_le_mul_of_nonneg_right (show 1-p≤1 by linarith) hη'
      linarith only [hh,hta,htb,hsa,hsb]
  have hh:=abs_add_le (markedSixDegreeBalance m d i-markedSixDegreeBalance m c i) (markedSixDegreeBalance m c i)
  have hsum:markedSixDegreeBalance m d i-markedSixDegreeBalance m c i+markedSixDegreeBalance m c i=
      markedSixDegreeBalance m d i:=by ring
  rw [hsum] at hh
  linarith only [hh,he,hc]
end Oberwolfach
