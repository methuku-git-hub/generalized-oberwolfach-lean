module

public import Oberwolfach.FirstVortexIndependentLoadBudgetEventually

@[expose] public section
/-! The matching spacing and host cutoff can be chosen after an arbitrary
positive sampling rate, by taking the cycle cutoff after the spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_independent_spacing_choice (r:ℕ) (θ:ℝ) (hθ:0<θ):
    ∃d K:ℕ,3≤d ∧ (r+4)+2≤d ∧ 3≤K ∧
      1/(d:ℝ)≤θ/1024 ∧
      (1/(((r+4):ℝ)+1))/(d:ℝ)≤θ ∧
      5/((((r+4):ℝ)+1)*(d:ℝ)+5)+(((r+4):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 :=by
  obtain ⟨N,hN⟩:=exists_nat_gt (1024/θ)
  let d:=max ((r+4)+2) (N+1)
  have hdN:N<d:=by dsimp [d];omega
  have hd:3≤d:=by dsimp [d];omega
  have hdl:(r+4)+2≤d:=le_max_left _ _
  have hdp:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hdn:(N:ℝ)<d:=by exact_mod_cast hdN
  have hrate:1024<θ*d:=by
    have h:=lt_trans hN hdn
    have hh:1024<(d:ℝ)*θ:=(div_lt_iff₀ hθ).mp h
    nlinarith
  have hspace:1/(d:ℝ)≤θ/1024:=by
    apply (div_le_iff₀ hdp).2
    nlinarith
  let m:ℝ:=((r+4):ℝ)+1
  have hm:1≤m:=by
    dsimp [m]
    have hr:(0:ℝ)≤r:=Nat.cast_nonneg _
    push_cast
    linarith
  have hmp:0<m:=by linarith
  obtain ⟨M,hM⟩:=exists_nat_gt (4*m*d/θ)
  let K:=max 3 (M+1)
  have hK:3≤K:=le_max_left _ _
  have hKM:M<K:=by dsimp [K];omega
  have hKp:0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  have hKMreal:(M:ℝ)<K:=by exact_mod_cast hKM
  have hSecond:m*d/(K:ℝ)≤θ/4:=by
    have hlt:4*m*d/θ<(K:ℝ):=lt_trans hM hKMreal
    have hh:4*m*d<(K:ℝ)*θ:=(div_lt_iff₀ hθ).mp hlt
    apply (div_le_iff₀ hKp).2
    nlinarith
  have hfirst:5/(m*d+5)≤5/(d:ℝ):=by
    apply div_le_div_of_nonneg_left (by norm_num) hdp
    nlinarith [mul_nonneg (show 0≤m-1 by linarith) hdp.le]
  have hfirstsmall:5/(m*d+5)≤θ/4:=by
    have heq:5/(d:ℝ)=5*(1/(d:ℝ)):=by ring
    linarith
  have hcut:(1/m)/(d:ℝ)≤θ:=by
    have hmrec:1/m≤1:=by apply (div_le_one hmp).2;linarith
    have hh:=div_le_div_of_nonneg_right hmrec hdp.le
    linarith
  refine ⟨d,K,hd,hdl,hK,hspace,?_,?_⟩
  · simpa only [m,Nat.cast_add,Nat.cast_ofNat] using hcut
  · have htotal:5/(m*d+5)+m*d/(K:ℝ)≤θ/2:=by linarith
    simpa only [m,Nat.cast_add,Nat.cast_ofNat] using htotal
end Oberwolfach
