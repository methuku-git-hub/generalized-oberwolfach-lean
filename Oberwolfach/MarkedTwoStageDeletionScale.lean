module

public import Oberwolfach.MarkedProtectedActiveDeletion

@[expose] public section

/-! The actual free-degree bounds of the two earlier packings fit a single
active deletion allowance. No degree bound at a covered root is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace Oberwolfach

theorem marked_two_stage_deletion_scale
    (r K:ℕ) (n tcard wcard etaE xi kappa:ℝ)
    (hn:0≤n) (he:0≤etaE) (hxi:0≤xi)
    (hT:tcard≤xi*n) (hW:wcard≤xi*n)
    (hE:(4*K+3*r+50:ℝ)*etaE≤kappa/2)
    (hX:(4*K+3*r+50:ℝ)*xi≤kappa/2):
    24*etaE*n+2*wcard+tcard*(4*(K+4))+2*tcard≤kappa*n∧
    6*etaE*n+wcard+tcard*(K+4)≤kappa*n∧
    3*(r+5)*etaE*n+tcard*(r+5)≤kappa*n:=by
  have hEn:=mul_le_mul_of_nonneg_right hE hn
  have hXn:=mul_le_mul_of_nonneg_right hX hn
  have hnR:0≤(r:ℝ):=Nat.cast_nonneg r
  have hnK:0≤(K:ℝ):=Nat.cast_nonneg K
  have heN:0≤etaE*n:=mul_nonneg he hn
  have hxN:0≤xi*n:=mul_nonneg hxi hn
  have he24:24*etaE*n≤(4*K+3*r+50:ℝ)*etaE*n:=by
    nlinarith only [mul_nonneg hnK heN,mul_nonneg hnR heN,heN]
  have he6:6*etaE*n≤(4*K+3*r+50:ℝ)*etaE*n:=by
    nlinarith only [mul_nonneg hnK heN,mul_nonneg hnR heN,heN]
  have heU:3*(r+5)*etaE*n≤(4*K+3*r+50:ℝ)*etaE*n:=by
    nlinarith only [mul_nonneg hnK heN,heN]
  have htR:=mul_le_mul_of_nonneg_right hT (show 0≤4*((K:ℝ)+4)+2 by positivity)
  have htV:=mul_le_mul_of_nonneg_right hT (show 0≤(K:ℝ)+4 by positivity)
  have htU:=mul_le_mul_of_nonneg_right hT (show 0≤(r:ℝ)+5 by positivity)
  have hxR:(4*K+20:ℝ)*xi*n≤(4*K+3*r+50:ℝ)*xi*n:=by
    nlinarith only [mul_nonneg hnR hxN,hxN]
  have hxV:(K+5:ℝ)*xi*n≤(4*K+3*r+50:ℝ)*xi*n:=by
    nlinarith only [mul_nonneg hnK hxN,mul_nonneg hnR hxN,hxN]
  have hxU:(r+5:ℝ)*xi*n≤(4*K+3*r+50:ℝ)*xi*n:=by
    nlinarith only [mul_nonneg hnK hxN,mul_nonneg hnR hxN,hxN]
  refine ⟨?_,?_,?_⟩
  · nlinarith only [he24,hEn,hXn,htR,hW,hxR]
  · nlinarith only [he6,hEn,hXn,htV,hW,hxV]
  · nlinarith only [heU,hEn,hXn,htU,hxU]

end Oberwolfach
