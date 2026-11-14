module

public import Oberwolfach.OrdinaryActualPhysicalRateBudget

@[expose] public section
/-! After the cycle-weight constants and matching robustness tolerance are
fixed, choose the sampling and deletion tolerances in their required order. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_matching_tolerances_after_weights
    (K:ℕ) (hK:0<K) (θ lam pstar ε loss cap:ℝ)
    (hθ:0<θ) (hlam:0<lam) (hlam1:lam≤1) (hp:0<pstar) (hε:0<ε) (hloss:0≤loss) (hcap:0<cap):
    ∃τ t ξ b:ℝ,0<τ ∧ 0<t ∧ 0<ξ ∧ 0<b ∧ b≤cap ∧
      τ≤1/2 ∧ τ≤lam*pstar/4 ∧ ξ≤lam*pstar/4 ∧ ξ≤pstar/2 ∧
      t+loss*b≤θ/(800*(K:ℝ)) ∧
      t+loss*b≤lam*(θ/(100*(K:ℝ)))/4 ∧
      4*((K:ℝ)+1)*(t+loss*b)+τ≤ε :=by
  have hKR:0<(K:ℝ):=by exact_mod_cast hK
  let q:ℝ:=min (θ/(800*(K:ℝ))) (min (lam*(θ/(100*(K:ℝ)))/4) (ε/(16*((K:ℝ)+1))))
  have hq:0<q:=by dsimp [q];positivity
  have hq1:q≤θ/(800*(K:ℝ)):=min_le_left _ _
  have hq2:q≤lam*(θ/(100*(K:ℝ)))/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hq3:q≤ε/(16*((K:ℝ)+1)):=(min_le_right _ _).trans (min_le_right _ _)
  let τ:ℝ:=min (1/4) (min (lam*pstar/8) (ε/4))
  let t:ℝ:=q/4
  let ξ:ℝ:=lam*pstar/8
  let b:ℝ:=min cap (q/(4*(loss+1)))
  have hτ:0<τ:=by dsimp [τ];positivity
  have ht:0<t:=by dsimp [t];positivity
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hb:0<b:=by dsimp [b];positivity
  have hbcap:b≤cap:=min_le_left _ _
  have hbq:b≤q/(4*(loss+1)):=min_le_right _ _
  have hbmult:loss*b≤q/4:=by
    have hden:0<4*(loss+1):=by positivity
    have hh:4*(loss+1)*b≤q:=by simpa [mul_comm] using (le_div_iff₀ hden).mp hbq
    nlinarith [mul_nonneg hb.le hloss]
  have hsum:t+loss*b≤q:=by dsimp [t];linarith
  have hτ1:τ≤1/4:=min_le_left _ _
  have hτ2:τ≤lam*pstar/8:=(min_le_right _ _).trans (min_le_left _ _)
  have hτ3:τ≤ε/4:=(min_le_right _ _).trans (min_le_right _ _)
  have hq3':16*((K:ℝ)+1)*q≤ε:=by
    simpa [mul_comm] using (le_div_iff₀ (by positivity : 0<16*((K:ℝ)+1))).mp hq3
  refine ⟨τ,t,ξ,b,hτ,ht,hξ,hb,hbcap,by linarith,by linarith,?_,?_,hsum.trans hq1,hsum.trans hq2,?_⟩
  · dsimp [ξ];linarith
  · dsimp [ξ];nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hlam1)]
  · have hh:=mul_le_mul_of_nonneg_left hsum (show 0≤4*((K:ℝ)+1) by positivity)
    nlinarith

theorem ordinary_matching_deleted_error_le_rate
    (n:ℕ) (hn:0<n) (t loss Δ b:ℝ) (hloss:0≤loss) (hΔ:Δ≤b*n):
    t+loss*Δ/(n:ℝ)≤t+loss*b :=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hh:Δ/(n:ℝ)≤b:=(div_le_iff₀ hnR).2 hΔ
  have hmul:=mul_le_mul_of_nonneg_left hh hloss
  have heq:loss*Δ/(n:ℝ)=loss*(Δ/(n:ℝ)):=by ring
  rw [heq]
  linarith
end Oberwolfach
