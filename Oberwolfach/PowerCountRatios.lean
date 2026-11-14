module

public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Explicit conversion of labelled configuration counts to reciprocal
power bounds. All denominator lower bounds are positive. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach

theorem power_count_ratio_bound (h s : ℕ) (hs : s ≤ h) (a k b K M z : ℝ)
    (ha : 0 < a) (hk : 0 < k) (hb : 1 ≤ b) (hK : 0 ≤ K)
    (hM : a*k^h ≤ M) (hz : z ≤ K*(b*k)^(h-s)) :
    z/M ≤ (K*b^h/a)/k^s := by
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  have hb0 : 0 ≤ b := by linarith
  have hpow : b^(h-s) ≤ b^h := pow_le_pow_right₀ hb (Nat.sub_le _ _)
  have hz' : z ≤ K*b^h*k^(h-s) := by
    rw [mul_pow] at hz
    exact hz.trans (by nlinarith [mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ K*k^(h-s))])
  have he : (K*b^h/a/k^s)*(a*k^h)=K*b^h*k^(h-s) := by
    have hh : k^h=k^(h-s)*k^s := by rw [← pow_add,Nat.sub_add_cancel hs]
    rw [hh]
    field_simp
  apply (div_le_iff₀ hM0).mpr
  calc
    z ≤ K*b^h*k^(h-s) := hz'
    _ = (K*b^h/a/k^s)*(a*k^h) := he.symm
    _ ≤ (K*b^h/a/k^s)*M := mul_le_mul_of_nonneg_left hM (by positivity)

end Oberwolfach
