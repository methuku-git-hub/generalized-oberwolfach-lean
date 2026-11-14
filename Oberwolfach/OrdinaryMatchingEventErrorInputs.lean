module

public import Oberwolfach.OrdinaryMatchingTolerancesAfterWeights

@[expose] public section
/-! Fixed tolerance choices give the exact relative-error and deletion-error
hypotheses consumed by the same-sample matching theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_matching_event_error_inputs
    (K n:ℕ) (hn:0<n) (θ lam pstar ε loss τ t ξ b Δ:ℝ)
    (hloss:0≤loss) (hτ0:0≤τ) (hξ0:0≤ξ)
    (hτhalf:τ≤1/2) (hτrate:τ≤lam*pstar/4)
    (hξrate:ξ≤lam*pstar/4) (hξhalf:ξ≤pstar/2) (hΔ:Δ≤b*n)
    (hterr1:t+loss*b≤θ/(800*(K:ℝ)))
    (hterr2:t+loss*b≤lam*(θ/(100*(K:ℝ)))/4)
    (hterr3:4*((K:ℝ)+1)*(t+loss*b)+τ≤ε):
    let countErr:=ξ*(n:ℝ)
    let terr:=t+loss*Δ/(n:ℝ);
    τ≤1/2 ∧ countErr≤pstar*n/2 ∧ 0≤τ ∧ 0≤countErr ∧
    τ≤lam*pstar/4 ∧ countErr≤lam*pstar*n/4 ∧ ξ*n≤countErr ∧
    terr≤θ/(800*(K:ℝ)) ∧ terr≤lam*(θ/(100*(K:ℝ)))/4 ∧
    4*((K:ℝ)+1)*terr+τ≤ε :=by
  intro countErr terr
  have hnR:0≤(n:ℝ):=by positivity
  have hcount:countErr≤pstar*n/2:=by
    dsimp [countErr]
    have hh:=mul_le_mul_of_nonneg_right hξhalf hnR
    nlinarith
  have hcountRate:countErr≤lam*pstar*n/4:=by
    dsimp [countErr]
    have hh:=mul_le_mul_of_nonneg_right hξrate hnR
    nlinarith
  have ht:terr≤t+loss*b:=by
    dsimp [terr]
    exact ordinary_matching_deleted_error_le_rate n hn t loss Δ b hloss hΔ
  have hmul:4*((K:ℝ)+1)*terr≤4*((K:ℝ)+1)*(t+loss*b):=
    mul_le_mul_of_nonneg_left ht (by positivity)
  refine ⟨hτhalf,hcount,hτ0,?_,hτrate,hcountRate,by rfl,ht.trans hterr1,ht.trans hterr2,?_⟩
  · dsimp [countErr];positivity
  · linarith
end Oberwolfach
